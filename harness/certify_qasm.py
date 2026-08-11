#!/usr/bin/env python3
"""
certify_qasm.py — real-circuit coverage harness, driver side (paper question E1).

This script does two jobs.

  1. `--samples`  : Certify the shipped basis-subset sample circuits. This
                    option calls the Lean entry point CertifyQASM.lean. This
                    job is fully reproducible here, with no extra dependencies.

  2. `--transpile`: (OPTIONAL, and you run it yourself) Transpile
                    real QASMBench / MQTBench circuits with Qiskit to the IBM
                    basis and a heavy-hex coupling map. The output is
                    basis-subset QASM that this harness can then certify.
                    This job needs `pip install qiskit` and the benchmark
                    files. We ship the pipeline. We do NOT ship fabricated
                    large-scale numbers.

Run from the Artifact/ project root (after `lake build`):
    python3 harness/certify_qasm.py --samples
"""
import argparse, glob, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
# The project root is one level above harness/ (the Artifact directory).
ROOT = os.path.abspath(os.path.join(HERE, ".."))
# Use the SOUND lexer. `CertifyQASM.lean` drives `parseQASM`. This lexer silently skips
# unrecognized tokens. As a result, it accepts circuits whose support it never saw (for
# example, a classically-conditioned `if(c==1) cz q[5],q[6];` on forbidden qubits).
# `CertifyQASMSafe.lean` drives `parseQASMSafe`, which rejects any unrecognized
# support-bearing statement outright (REJECT-PARSE).
LEAN_ENTRY = os.path.relpath(os.path.join(HERE, "CertifyQASMSafe.lean"), ROOT)
LEAN = os.path.expanduser("~/.elan/bin/lean")
LAKE = os.path.expanduser("~/.elan/bin/lake")


def certify(qasm_paths):
    """Invoke the Lean validator on the given QASM files. Stream the verdicts from the validator."""
    if not qasm_paths:
        print("no QASM files to certify", file=sys.stderr)
        return 1
    cmd = [LAKE, "env", LEAN, "--run", LEAN_ENTRY] + qasm_paths
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ.get("PATH", ""))
    return subprocess.call(cmd, cwd=ROOT, env=env)


def run_samples():
    samples = sorted(glob.glob(os.path.join(HERE, "samples", "*.qasm")))
    print(f"# certifying {len(samples)} shipped sample circuits\n")
    return certify([os.path.relpath(p, ROOT) for p in samples])


TRANSPILE_RECIPE = r'''
# --- OPTIONAL, run externally: reproduce the E1 corpus at scale ----------------
# You run this step yourself. We ship the pipeline. We do NOT ship fabricated numbers.
#
#   pip install qiskit
#
# Then, per benchmark circuit (for example, from QASMBench small/medium or MQTBench):
#
#   from qiskit import QuantumCircuit, transpile
#   from qiskit.transpiler import CouplingMap
#   # 12-node heavy-hex ring used by the Lean device model `heavyHex`:
#   ring = CouplingMap([[i, (i + 1) % 12] for i in range(12)])
#   qc = QuantumCircuit.from_qasm_file("bench.qasm")
#   tqc = transpile(qc, coupling_map=ring, basis_gates=["x", "sx", "rz", "cz", "id"],
#                   optimization_level=3)
#   open("bench.transpiled.qasm", "w").write(tqc.qasm())   # or dumps() on Qiskit >=1.0
#
# Feed the transpiled files back:  certify_qasm.py --files bench.transpiled.qasm ...
# Metrics to report: accept/reject per circuit, false-reject rate (a confined circuit
# wrongly rejected — must be 0), and parse-coverage (fraction of gates the basis-subset
# lexer recognizes). Scope honestly. Circuits must fit the 12-node ring and basis subset.
# Larger devices need the coupling map and n generalized in the Lean model first.
'''


def main():
    ap = argparse.ArgumentParser(description="Validate OpenQASM-subset circuits with the Lean validator.")
    ap.add_argument("--samples", action="store_true", help="certify the shipped sample circuits")
    ap.add_argument("--files", nargs="*", help="certify specific QASM files")
    ap.add_argument("--transpile-recipe", action="store_true",
                    help="print the (external) Qiskit transpile recipe for scale-up")
    args = ap.parse_args()

    if args.transpile_recipe:
        print(TRANSPILE_RECIPE)
        return 0
    if args.files:
        return certify(args.files)
    if args.samples or not (args.files or args.transpile_recipe):
        return run_samples()
    return 0


if __name__ == "__main__":
    sys.exit(main())
