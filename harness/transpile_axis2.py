#!/usr/bin/env python3
"""Axis-2 at scale. This script transpiles real QASMBench circuits to the ring
and basis subset of the Lean device model, under two tenant-layout regimes.
The script writes basis-subset QASM as output."""
import os, glob, sys, json, traceback, pathlib
from qiskit.qasm2 import load, dumps, LEGACY_CUSTOM_INSTRUCTIONS
from qiskit import transpile
from qiskit.transpiler import CouplingMap

HERE = pathlib.Path(__file__).resolve().parent
# QASMBench (PNNL) is an external benchmark suite. This artifact does not ship it.
# Clone QASMBench yourself. Then point QASMBENCH_SMALL at its small/ subdirectory.
# Or accept the default below (HERE/QASMBench/small).
SMALL = os.environ.get("QASMBENCH_SMALL", str(HERE / "QASMBench" / "small"))
OUT   = os.environ.get("AXIS2_OUT", str(HERE / "axis2-out"))
BASIS = ["x", "sx", "rz", "cz", "id"]
os.makedirs(f"{OUT}/confinedA", exist_ok=True)
os.makedirs(f"{OUT}/fullB", exist_ok=True)

# Lean model: heavyHex is a 12-node ring. Tenant A ({0..5}) path edges are ring edges.
RING12  = CouplingMap([[i, (i + 1) % 12] for i in range(12)])
PATH6   = CouplingMap([[i, i + 1] for i in range(5)])            # nodes 0..5 (a ring sub-path)

# These are the lexer basis-subset tokens for parse coverage. The parse-coverage
# calculation excludes non-gate lines from the denominator.
GATE_PREFIXES = ("x ", "sx ", "id ", "rz", "cz ", "cx ")
NONGATE = ("OPENQASM", "include", "qreg", "creg", "gate ", "barrier", "measure",
           "reset", "//", "opaque", "if(")

def strip_nonunitary(qc):
    qc = qc.remove_final_measurements(inplace=False) or qc
    from qiskit.converters import circuit_to_dag, dag_to_circuit
    dag = circuit_to_dag(qc)
    for node in list(dag.op_nodes()):
        if node.op.name in ("measure", "reset", "barrier"):
            dag.remove_op_node(node)
    return dag_to_circuit(dag)

def parse_coverage(qasm_text):
    gate_lines = recog = 0
    for raw in qasm_text.splitlines():
        s = raw.strip()
        if not s or s.startswith(NONGATE):
            continue
        gate_lines += 1
        if s.startswith(GATE_PREFIXES):
            recog += 1
    return recog, gate_lines

rows = []
for d in sorted(glob.glob(f"{SMALL}/*_n*")):
    name = os.path.basename(d)
    src = os.path.join(d, name + ".qasm")
    if not os.path.exists(src):
        continue
    rec = {"name": name}
    try:
        qc = load(src, include_path=(d, SMALL), custom_instructions=LEGACY_CUSTOM_INSTRUCTIONS)
        qc = strip_nonunitary(qc)
        nq = qc.num_qubits
        rec["nq"] = nq
        # Regime B: the full 12-node ring, unconstrained. The transpiler can use nodes {6..11}.
        if nq <= 12:
            tB = transpile(qc, coupling_map=RING12, basis_gates=BASIS, optimization_level=3, seed_transpiler=7)
            txtB = dumps(tB)
            open(f"{OUT}/fullB/{name}.qasm", "w").write(txtB)
            r, g = parse_coverage(txtB)
            rec["B"] = {"cov_recog": r, "cov_total": g}
        # Regime A: confined to the tenant sub-lattice {0..5}. Only circuits that fit run in this regime.
        if nq <= 6:
            tA = transpile(qc, coupling_map=PATH6, basis_gates=BASIS, optimization_level=3, seed_transpiler=7)
            txtA = dumps(tA)
            open(f"{OUT}/confinedA/{name}.qasm", "w").write(txtA)
            r, g = parse_coverage(txtA)
            rec["A"] = {"cov_recog": r, "cov_total": g}
    except Exception as e:
        rec["error"] = f"{type(e).__name__}: {e}"[:160]
    rows.append(rec)

json.dump(rows, open(f"{OUT}/manifest.json", "w"), indent=1)
ok  = [r for r in rows if "error" not in r]
err = [r for r in rows if "error" in r]
print(f"loaded+transpiled: {len(ok)}   skipped(load/transpile error): {len(err)}")
print(f"  confinedA files: {len(glob.glob(OUT+'/confinedA/*.qasm'))}   fullB files: {len(glob.glob(OUT+'/fullB/*.qasm'))}")
for r in err:
    print(f"  SKIP {r['name']}: {r['error']}")
