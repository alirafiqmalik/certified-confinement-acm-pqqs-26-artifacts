# Certified Confinement: artifact

A tenant-side **validator** for untrusted quantum-cloud transpiler output, with a
kernel-checked soundness proof in Lean 4.

Given the device coupling graph, a forbidden region, and the circuit the
transpiler emitted, the validator decides two structural predicates: the circuit
is hardware-legal, and no non-identity gate touches the forbidden region or its
`k`-hop neighbourhood. It never simulates quantum state.

## Run it

```bash
bash run_artifact.sh
```

One command. No IBM account and no quantum hardware. About **3 minutes** after
the Lean library is built. Results go to `artifact-run/SUMMARY.md`.

If `lake` or the Python environment is missing, read [SETUP.md](SETUP.md) first.

## What passes

A complete offline run reports **18 stages, 0 failures**. The stages that carry
the paper's numbers:

| stage | check | expected |
|---|---|---|
| A2 | axiom base | `certifySecurity_sound` rests on `[propext]` alone |
| A4 | 11 real device topologies | `ALL 11 DEVICES PASS (44 verdicts recomputed independently)` |
| A5 | 4 sample circuits | 2 ACCEPT, 2 REJECT |
| A7 | offline regression suite | `9/9 tests passed` |
| A9 | published hardware numbers | `8/8` sweep and `8/8` repeat cells reproduce from raw counts |
| B2 | QASMBench sweep | violation rate 18 / 53 / 71 / 71 % at optimization levels 0–3 |
| B4 | front-end fuzzing | old lexer 269 false accepts, sound lexer 0 |

Stage A5 is the shortest way to see the point of the work:

```
ACCEPT  harness/samples/01_ok_confined.qasm    (gates=7 legal=true  confined=true)
REJECT  harness/samples/02_cotenant_touch.qasm (gates=3 legal=true  confined=false)
REJECT  harness/samples/03_illegal_edge.qasm   (gates=2 legal=false confined=false)
ACCEPT  harness/samples/04_ok_ring_chain.qasm  (gates=8 legal=true  confined=true)
```

Sample 02 is hardware-legal and still rejected: it places the tenant's qubits
next to a forbidden co-tenant region. A hardware-legality check alone cannot see
that.

Stage A9 audits every hardware number in the paper **offline**, from raw
bitstring counts. No account, no QPU, no network.

## The other documents

| file | what is in it |
|---|---|
| [SETUP.md](SETUP.md) | toolchains, build times, optional benchmark suite, IBM credentials |
| [USAGE.md](USAGE.md) | every stage, how to run it alone, and what it prints |
| [PAPER.md](PAPER.md) | how each claim of the paper maps to a file and a symbol |

## Layout

```
run_artifact.sh        one entry point for every result
setup.sh               creates the Python environment
QpuCompiler/           the Lean 4 / Mathlib library (22 files)
harness/
  samples/             4 QASM circuits with known verdicts
  devices/             11 real device topologies and an independent re-verifier
  eval-scripts/        QASMBench sweep, fuzzing, buffered-policy sweeps
  axis2-results/       committed results of the benchmark run
  sim/                 offline forward model and the 9-test suite
  ibm-hardware/        IBM submission and collection scripts, and the measurements
```

Every `.md` file under `harness/` reports one set of results and states its own
limits.

## Two things to know

**The repository ships the results the paper reports.** A new run writes to
`artifact-run/` and leaves them alone. Only `--submit-qpu` replaces them, and it
backs them up first.

**The proof covers structure, not physics.** An accepted certificate says no
gate of the circuit touches the forbidden region or a qubit within `k` hops of
it. It is not a bound on the magnitude of crosstalk. [PAPER.md](PAPER.md) states
the full scope.
