#!/usr/bin/env python3
"""run_buffered_alloc.py — is the buffered policy OPERABLE?

`run_buffered.py` certifies the existing axis-2 corpus against the k-hop buffered
region and rejects almost everything. This is not a property of the policy. It is
a property of the *allocation*. Tenant A = {0..5} and the k=1 buffer around
F = {6..11} both claim qubits 0 and 5. So every circuit that touches the ends of
the tenant's path is a violation by construction.

A buffer only means something if the DEVICE carves it out, not the tenant. This
script models the deployment that makes sense: the provider reserves the k-hop
halo around the co-tenant as a dead zone, and the tenant gets what is left.

  k=0 -> allowed {0,1,2,3,4,5}   (6 qubits, no buffer)
  k=1 -> allowed {1,2,3,4}       (4 qubits, 0 and 5 reserved)
  k=2 -> allowed {2,3}           (2 qubits)
  k=3 -> allowed {}              (ring is fully sterilized)

For each k, we give the transpiler ONLY the induced subgraph on the allowed set.
This is the "restricted coupling map" discipline that DynQ assumes but does not
check. Then we use the Lean certifier to verify that the transpiler actually
stayed inside it. Two numbers come out:

  * operability : accept rate for circuits that FIT the allowed set. A policy that
                  cannot accept anything is not a policy.
  * capacity    : how many qubits the tenant loses to the buffer, and how many
                  benchmark circuits stop fitting as a result.

Usage (from the Artifact/ root, after `lake build`):
    QASMBENCH_SMALL=... AXIS2_OUT=... python3 harness/eval-scripts/run_buffered_alloc.py
"""
import os, glob, json, pathlib, re, subprocess, argparse
from qiskit.qasm2 import load, dumps, LEGACY_CUSTOM_INSTRUCTIONS
from qiskit import transpile
from qiskit.transpiler import CouplingMap
from qiskit.converters import circuit_to_dag, dag_to_circuit

HERE = pathlib.Path(__file__).resolve().parent
ROOT = os.environ.get("ARTIFACT_ROOT", str(HERE.parents[1]))
SMALL = os.environ.get("QASMBENCH_SMALL", str(HERE.parent / "QASMBench" / "small"))
OUT = os.environ.get("AXIS2_OUT", str(HERE.parent / "axis2-out"))
BASIS = ["x", "sx", "rz", "cz", "id"]
LAKE = os.path.expanduser("~/.elan/bin/lake")
LEAN = os.path.expanduser("~/.elan/bin/lean")
ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ.get("PATH", ""))
ENTRY = "harness/CertifyQASMBuffered.lean"

ap = argparse.ArgumentParser()
ap.add_argument("--kmax", type=int, default=2)
ap.add_argument("--out", default=str(HERE / "buffered_alloc_results.json"))
args = ap.parse_args()

N = 12
RING = [(i, (i + 1) % N) for i in range(N)]
FORBIDDEN = set(range(6, 12))


def buffered(k):
    """k-hop closure of FORBIDDEN over the ring -- mirrors Lean `bufferK heavyHex tenantF k`."""
    blocked = set(FORBIDDEN)
    for _ in range(k):
        blocked |= {b for (u, v) in RING for b in ((u,) if v in blocked else ()) + ((v,) if u in blocked else ())}
    return blocked


def strip(qc):
    qc = qc.remove_final_measurements(inplace=False) or qc
    dag = circuit_to_dag(qc)
    for n in list(dag.op_nodes()):
        if n.op.name in ("measure", "reset", "barrier"):
            dag.remove_op_node(n)
    return dag_to_circuit(dag)


srcs = []
for d in sorted(glob.glob(f"{SMALL}/*_n*")):
    name = os.path.basename(d)
    p = os.path.join(d, name + ".qasm")
    if not os.path.exists(p):
        continue
    try:
        srcs.append((name, strip(load(p, include_path=(d, SMALL),
                                      custom_instructions=LEGACY_CUSTOM_INSTRUCTIONS))))
    except Exception:
        continue

results = {}
for k in range(args.kmax + 1):
    blocked = buffered(k)
    allowed = sorted(set(range(N)) - blocked)
    edges = [[u, v] for (u, v) in RING if u in allowed and v in allowed]
    edges += [[v, u] for [u, v] in edges]
    outdir = f"{OUT}/alloc_k{k}"
    os.makedirs(outdir, exist_ok=True)
    if not allowed:
        results[f"k{k}"] = dict(allowed=[], n_allowed=0, note="ring fully sterilised; no allocation possible")
        print(f"k={k}  allowed=0/12  -- ring fully sterilised, no circuits can run")
        continue
    cmap = CouplingMap(edges) if edges else None
    fits = skipped = 0
    per_opt = {}
    for opt in (0, 1, 2, 3):
        n_written = 0
        for name, qc in srcs:
            if qc.num_qubits > len(allowed):
                continue
            try:
                t = transpile(qc, coupling_map=cmap, basis_gates=BASIS,
                              optimization_level=opt, seed_transpiler=7,
                              initial_layout=allowed[:qc.num_qubits] if cmap else None)
                open(f"{outdir}/o{opt}_{name}.qasm", "w").write(dumps(t))
                n_written += 1
            except Exception:
                pass
        per_opt[opt] = n_written
    fits = sum(1 for _, qc in srcs if qc.num_qubits <= len(allowed))
    skipped = len(srcs) - fits

    files = [os.path.relpath(f, ROOT) for f in sorted(glob.glob(f"{outdir}/*.qasm"))]
    r = subprocess.run([LAKE, "env", LEAN, "--run", ENTRY, str(k)] + files,
                       cwd=ROOT, env=ENV, capture_output=True, text=True)
    verds = {}
    for ln in r.stdout.splitlines():
        m = re.match(r"(ACCEPT|REJECT|REJECT-PARSE)\s+(\S+)", ln)
        if m:
            verds[m.group(2)] = m.group(1)
    summary = {}
    for opt in (0, 1, 2, 3):
        fs = [f for f in files if os.path.basename(f).startswith(f"o{opt}_")]
        vs = [verds[f] for f in fs if f in verds]
        summary[f"opt{opt}"] = dict(
            n=len(vs),
            accept=sum(1 for v in vs if v == "ACCEPT"),
            reject=sum(1 for v in vs if v == "REJECT"),
            reject_parse=sum(1 for v in vs if v == "REJECT-PARSE"),
        )
    results[f"k{k}"] = dict(allowed=allowed, n_allowed=len(allowed),
                            circuits_fitting=fits, circuits_too_large=skipped,
                            summary=summary)
    acc = {o: f"{summary[o]['accept']}/{summary[o]['n']}" for o in summary}
    print(f"k={k}  allowed={len(allowed)}/12 {allowed}  fits={fits}/{len(srcs)}  accept by opt={acc}")

json.dump(results, open(args.out, "w"), indent=1)
print(f"\nwrote {args.out}")
