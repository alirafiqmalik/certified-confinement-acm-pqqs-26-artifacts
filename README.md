# Artifact — Trust-but-Verify the Transpiler

This repository contains a Lean 4 / Mathlib library and a Python harness.
Together, they reproduce the results of the paper.

The paper gives per-instance certificates that the Lean kernel checks. Each
certificate shows that the output of an **untrusted** quantum-cloud transpiler
is legal on the hardware graph. The certificate also shows that the output
stays confined to the region of one tenant. Confinement means that the qubits
of a client never share a qubit or a coupling edge with a co-tenant. The cost
of the check is linear in the size of the program. The check runs on the
output of any compiler.

---

## 1. Reproduce everything with one command

```bash
bash run_artifact.sh
```

The script builds the Lean library, runs every check, and writes a summary to
`artifact-run/SUMMARY.md`. It needs no IBM account and no quantum hardware.
After the first Lean build, the script takes about **3 minutes**.

The table below lists further options.

| command | what it adds | what it needs |
|---|---|---|
| `bash run_artifact.sh` | the full offline reproduction | Lean + Python |
| `bash run_artifact.sh --core-only` | the offline reproduction, minus the optional tiers | Lean + Python |
| `bash run_artifact.sh --fetch-benchmarks` | the sweep over the QASMBench circuit suite | a network connection |
| `bash run_artifact.sh --submit-qpu` | new measurements on real IBM hardware | `apikey.json` and about 8 minutes of metered QPU time |

`bash run_artifact.sh --help` prints the same table with more detail.

## 2. Install the two toolchains

**Lean.** If `lake` is already on your PATH, skip this step.

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
export PATH="$HOME/.elan/bin:$PATH"
```

**Python.** If `.venv/` is missing, `run_artifact.sh` calls `setup.sh` for you.

```bash
bash setup.sh
```

The first `lake build` compiles Mathlib and can take 30 minutes or more. Every
later run replays the cache and takes seconds.

## 3. What you see

`run_artifact.sh` prints one line for each stage. The table below shows the
expected result of a complete offline run.

| stage | what it checks | expected output |
|---|---|---|
| A1 | the Lean library builds and the kernel accepts it | `Build completed successfully (2381 jobs)` |
| A2 | the axiom base of the main theorems | `certifySecurity_sound` depends on `[propext]` only |
| A3 | no proof leaves the kernel | `clean: no sorry / native_decide / ofReduceBool` |
| A4 | the 11-device corpus | `ALL 11 DEVICES PASS (44 verdicts recomputed independently)` |
| A5 | the 4 sample circuits | 2 ACCEPT, 2 REJECT (see below) |
| A6 | the cost of the checker against gate count | 4 rows, time grows with the gate count |
| A7 | the offline simulator suite | `9/9 tests passed` |
| A8 | the design of the follow-up measurement | `tau = 29 us` separates the alias branches |
| A9 | the published hardware numbers, recomputed from raw counts | `8/8` and `8/8` cells reproduce |

Stage A5 prints:

```
ACCEPT  harness/samples/01_ok_confined.qasm    (gates=7 legal=true  confined=true)
REJECT  harness/samples/02_cotenant_touch.qasm (gates=3 legal=true  confined=false)
REJECT  harness/samples/03_illegal_edge.qasm   (gates=2 legal=false confined=false)
ACCEPT  harness/samples/04_ok_ring_chain.qasm  (gates=8 legal=true  confined=true)
```

Sample 02 is the central example. The circuit is legal on the hardware graph.
The checker still rejects it, because it puts the qubits of the client next
to a forbidden co-tenant region. A check of hardware legality alone cannot see
that gap. This artifact exists to close it.

Stage A9 needs no account and no QPU. It recomputes every hardware number that
the paper reports, from the raw bitstring counts in
`harness/ibm-hardware/provenance.json`.

### Why the corpus check deletes build products first

`lake build` replays a cached `.olean` and reports success without re-checking a
single `decide`. Stage A4 deletes the build products of the corpus module first,
so the kernel must verify all 44 verdicts again. It then recomputes every verdict
outside the generated file, so a fault in the code generator cannot pass
silently.

## 4. Where each claim of the paper lives

| claim | file | symbol |
|---|---|---|
| C1 one certifier call over arbitrary output | `QpuCompiler/Confine.lean` | `certifySecurity`, `certifySecurity_sound` |
| C1 untrusted QASM ingestion | `QpuCompiler/Frontend.lean` | `parseQASMSafe` (sound), `parseQASM` (the unsound counterexample) |
| C2 symbolic routing, equal up to global phase | `QpuCompiler/CompileHH.lean`, `RouteEdge.lean` | `route_hh_congPhase`, `routeEdge_congPhase` |
| C2 routing keeps confinement | `QpuCompiler/Confine.lean` | `route_hh_confine`, `routeEdge_confined` |
| C3 confinement after route and optimise | `QpuCompiler/Confine.lean` | `compile_hh_confine_correct`, `optimize_conf` |
| C3 the degree-3 example | `QpuCompiler/Confine.lean` | `heavyHexFrag`, `fragF` |
| C3 confinement with a neighbour buffer | `QpuCompiler/Buffer.lean` | `bufferF`, `bufferK`, `compile_hh_confine_buffered` |
| C3 constant-time buffered queries | `QpuCompiler/Buffer.lean` | `bufferArr`, `bufferMemo`, `certifySecurity_bufferMemo` |
| C4 the cost is linear in the gate count | `QpuCompiler/Frontend.lean` | `checkerSteps`, `checkerSteps_seq` |
| generic device encoding | `QpuCompiler/DeviceLib.lean` | `EdgeSpec`, `EdgeSpec.toCoupling` |
| axis-1 caught-violation witnesses | `QpuCompiler/EvalWitnesses.lean` | `wA`, `wB`, `wC` |
| hostile-transpiler witnesses | `QpuCompiler/AdvWitnesses.lean` | `w1`, `w2full`, `w2skipped` |
| the bridge to the measured hardware leak | `QpuCompiler/HeronMarrakesh.lean` | `heronMarrakesh`, `Fd1`, `Ffar`, `victimCirc` |
| axis-2 ingestion of real circuits | `harness/` | `CertifyQASMSafe.lean`, `certify_qasm.py`, `samples/` |
| axis-3 wall-clock timing | `harness/` | `Timing.lean` |
| 11 real device topologies, 7 to 156 qubits | `harness/devices/` | `gen_device_corpus.py`, `DEVICE-CORPUS.md` |
| offline forward model and 9-test suite | `harness/sim/` | `qpu_sim.py`, `test_e2e.py`, `RESULTS-SIM.md` |
| blind leak prediction from public metadata | `harness/sim/` | `blind_predict.py`, `blind_score.py`, `BLIND-EMULATION.md` |
| live IBM hardware runs | `harness/ibm-hardware/` | `submit_*.py`, `collect_*.py`, `IBM-RESULTS.md` |

## 5. Directory layout

```
Artifact/
├── run_artifact.sh           # one entry point for every result
├── setup.sh                  # creates the Python environment
├── lakefile.toml, lean-toolchain, lake-manifest.json
├── QpuCompiler.lean          # library root; imports every module below
├── QpuCompiler/              # the proved Lean 4 / Mathlib library (22 files)
└── harness/
    ├── CertifyQASM*.lean, Timing*.lean   # the Lean side of the harness
    ├── certify_qasm.py, transpile_axis2.py
    ├── samples/              # 4 QASM circuits with known verdicts
    ├── devices/              # the 11-device corpus and its re-verifier
    ├── eval-scripts/         # fuzzing, optimisation-level sweep, comparisons
    ├── axis2-results/        # results of the benchmark-circuit run
    ├── sim/                  # offline forward model and 9-test suite
    └── ibm-hardware/         # IBM submission and collection scripts, plus results
```

Every `.md` file under `harness/` reports one set of results and states its own
limits.

## 6. Results that this repository ships

The repository ships the results of the run that the paper reports. A new run
writes to `artifact-run/` and leaves them unchanged. The one exception is
`--submit-qpu`, which replaces the hardware records. This flag backs up the
old records first. The command `git checkout -- harness/ibm-hardware` also
restores them.

## 7. Real hardware

`harness/ibm-hardware/` holds the scripts that produced the live-device numbers,
plus the raw result files.

You do **not** need hardware to audit those numbers. Stage A9 recomputes all 16
published cells from raw bitstring counts. The check runs offline.

To measure again on real hardware, copy `apikey.json.example` to `apikey.json`.
Paste an IBM Quantum token into the new file. Then run
`bash run_artifact.sh --submit-qpu`. Real device time is metered. The IBM open
plan grants 10 minutes per month. A full campaign uses about 8 of those
minutes. Check your remaining allowance first.

## 8. Scope of the claims

**The certificate.** `certifySecurity` certifies *any* transpiler output in
polynomial time. Functional equivalence is a separate, *bounded* result. It is
exact for small circuits and for the routing fragment only. We never claim it
for arbitrary output at scale, because that problem is QMA-complete.

**Confinement.** Confinement here means confinement of support: no co-location
on a forbidden qubit, for an allowed region `A`, a forbidden region `F`, and
secrets `S ⊆ A`. It is not general information-flow non-interference.

**Device models.** There are five: the 12-node heavy-hex ring `heavyHex`, the
degree-3 fragment `heavyHexFrag`, and the 14-qubit `heronPatch`. There is also
the measured `ibm_marrakesh` neighbourhood `heronMarrakesh`. The fifth is a
corpus of 11 real IBM topologies, from 7 to 156 qubits, in `DeviceCorpus.lean`.

**The OpenQASM lexer.** It covers the basis subset `{x, sx, id, rz, cz/cx}` and
it is **untrusted**. Use `parseQASMSafe`, which rejects any statement it does
not recognise. Do not use `parseQASM` for anything except the counterexample.
It drops unrecognised statements silently. A fuzz run turned 269 of 1120
crafted inputs into false accepts through that hole. The guarantee of either
lexer rests on `certifySecurity_sound` over the resulting circuit.

**Real-hardware claims.** The certificate proves *structural* non-adjacency on a
coupling graph. It is not a bound on the magnitude of crosstalk. The bridge to a
measured leak covers a small number of devices, victims and calibration
snapshots. `harness/ibm-hardware/IBM-RESULTS.md`, `SWEEP-RESULTS.md` and
`PROVENANCE.md` give the exact counts and the limits.

## 9. Axiom base

Stage A2 prints this output. To run it alone:

```bash
lake env lean --run - <<'EOF'
import QpuCompiler
#print axioms QpuCompiler.certifySecurity_sound        -- [propext]
#print axioms QpuCompiler.compile_hh_confine_correct   -- [propext, Classical.choice, Quot.sound]
#print axioms QpuCompiler.compile_hh_confine_buffered  -- [propext, Classical.choice, Quot.sound]
#print axioms QpuCompiler.EdgeSpec.toCoupling          -- [propext, Quot.sound]
#print axioms QpuCompiler.checkerSteps_seq             -- (no axioms)
EOF
```

The tree contains no `native_decide` and no `Lean.ofReduceBool`. Every `decide`
witness reduces inside the kernel under the three standard axioms.
