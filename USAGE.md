# Usage

`run_artifact.sh` is the entry point. Every stage below can also be run alone.

```bash
bash run_artifact.sh                    # tiers A and C
bash run_artifact.sh --core-only        # tier A only
bash run_artifact.sh --fetch-benchmarks # tiers A, B and C
bash run_artifact.sh --submit-qpu       # tiers A, C and D — costs metered QPU time
bash run_artifact.sh --help
```

Each stage writes `artifact-run/logs/<stage>.log`. The run writes
`artifact-run/SUMMARY.md`. A failing stage does not stop the run; the script
exits non-zero if any stage failed.

## The four tiers

| tier | needs | costs |
|---|---|---|
| A core | Lean and Python | nothing |
| B benchmarks | QASMBench | nothing |
| C hardware records | `apikey.json` | nothing; read-only retrieval |
| D live QPU | `apikey.json` and `--submit-qpu` | about 8 minutes of metered QPU time |

Tier A always runs. Tier B runs when QASMBench is present. Tier C runs when
`apikey.json` is present. Tier D runs only with the explicit flag.

---

## Tier A — core

### A1 · build and kernel-check the Lean library

```bash
lake build
```

`Build completed successfully (2381 jobs)`.

### A2 · axiom base

```bash
lake env lean --run - <<'EOF'
import QpuCompiler
#print axioms QpuCompiler.certifySecurity_sound
#print axioms QpuCompiler.compile_hh_confine_correct
#print axioms QpuCompiler.compile_hh_confine_buffered
#print axioms QpuCompiler.EdgeSpec.toCoupling
#print axioms QpuCompiler.checkerSteps_seq
def main : IO Unit := pure ()
EOF
```

```
'QpuCompiler.certifySecurity_sound' depends on axioms: [propext]
'QpuCompiler.compile_hh_confine_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'QpuCompiler.compile_hh_confine_buffered' depends on axioms: [propext, Classical.choice, Quot.sound]
'QpuCompiler.EdgeSpec.toCoupling' depends on axioms: [propext, Quot.sound]
'QpuCompiler.checkerSteps_seq' does not depend on any axioms
```

The stage fails if the soundness theorem gains any axiom beyond `propext`, or if
anything in the list uses an axiom outside the standard three.

### A3 · no proof leaves the kernel

Greps `QpuCompiler/` and `harness/*.lean` for `sorry`, `native_decide`, and
`ofReduceBool`. The pattern ignores the names inside backticks, because the
comments discuss them.

### A4 · the 11-device corpus

```bash
bash harness/devices/verify_corpus.sh
```

```
ALL 11 DEVICES PASS (44 verdicts recomputed independently)
clean: no sorry / native_decide / ofReduceBool / axiom
```

This does two things `lake build` does not. It deletes the build products of the
corpus module first, because Lake replays a cached `.olean` and reports success
without re-checking a single `decide`. It then recomputes all four verdicts per
device **outside** the generated file, so a fault in the code generator surfaces
as a FAIL instead of a silent pass.

To regenerate the corpus itself:

```bash
.venv/bin/python harness/devices/gen_device_corpus.py
```

That rewrites `QpuCompiler/DeviceCorpus.lean` and `harness/devices/corpus_meta.json`.
It reproduces the committed files byte for byte.

### A5 · the 4 sample circuits

```bash
.venv/bin/python harness/certify_qasm.py --samples
```

```
ACCEPT  harness/samples/01_ok_confined.qasm    (gates=7 legal=true  confined=true)
REJECT  harness/samples/02_cotenant_touch.qasm (gates=3 legal=true  confined=false)
REJECT  harness/samples/03_illegal_edge.qasm   (gates=2 legal=false confined=false)
ACCEPT  harness/samples/04_ok_ring_chain.qasm  (gates=8 legal=true  confined=true)
```

`legal` is `hardwareLegal` and `confined` is `policyConfined`. Sample 02 is the
gap this work closes: legal on the coupling graph, rejected by policy.

To validate your own circuits:

```bash
.venv/bin/python harness/certify_qasm.py --files a.qasm b.qasm
```

The driver uses `harness/CertifyQASMSafe.lean`, which drives the **sound** lexer.
`harness/CertifyQASM.lean` drives the unsound one and exists only as the
counterexample.

### A6 · validator cost against gate count

```bash
lake env lean --run harness/Timing.lean
```

```
gates_g,checker_steps,wall_ns
10,11,...
100,101,...
1000,1001,...
10000,10001,...
```

`checkerSteps` on an n-gate line circuit is exactly n+1. The wall-clock column
corroborates it; the proof is `checkerSteps_seq`.

### A7 · the offline regression suite

```bash
.venv/bin/python harness/sim/test_e2e.py
```

`9/9 tests passed`. Nine tests, no QPU:

| test | what it checks |
|---|---|
| T1 | an injected leak is detected |
| T2 | zero coupling gives no detection |
| T3 | measured ΔP → fitted ζ → simulated ΔP closes on itself |
| T4 | a plain Ramsey is blind; the Y basis is necessary |
| T5 | ΔP tracks \|sin(2πζτ)\| across a ζ sweep |
| T6 | one τ cannot pin ζ; the aliases are reported, not hidden |
| T7 | fitted ζ sits in a physically plausible band |
| T8 | Lean verdicts on the real device patch, via `lake env lean` |
| T9 | blind structural prediction scored against held-out hardware |

T3 is self-consistency of a forward model, not independent validation. Aer
contains no crosstalk; the ZZ term is injected by construction.

### A8 · the alias-resolving follow-up

```bash
.venv/bin/python harness/sim/tau_discriminator.py
```

Designs the single extra measurement that would separate the ζ alias branches:
τ = 29 µs, about 22 QPU-seconds. Pre-registered, not yet run.

### A9 · the published hardware numbers, offline

```bash
.venv/bin/python harness/ibm-hardware/reconcile_provenance.py
```

```
sweep : 8/8 published cells reproduce from raw counts; d1 leaking 7/8, d2 leaking 0/8
repeat: 8/8 published cells reproduce from raw counts; d1 leaking 8/8, d2 leaking 0/8
```

This is the stage to run if you want to audit the hardware claims without an
account. It recomputes every published cell from the raw bitstring counts in
`provenance.json` and reports the two cancelled arms that returned no data.

---

## Tier B — QASMBench

Needs QASMBench. See [SETUP.md](SETUP.md). All output goes to `artifact-run/`;
the committed results stay untouched.

| stage | script | what it produces |
|---|---|---|
| B1 | `eval-scripts/run_optlevel.py` | transpiles the suite at optimization levels 0–3 |
| B2 | `eval-scripts/run_e5b.py` | validator verdicts per level → 18 / 53 / 71 / 71 % violation |
| B3 | `eval-scripts/fuzz_e3.py` | generates the 1120-mutant corpus, seed 7 |
| B4 | `eval-scripts/fuzz_certify.py` | old lexer 269 false accepts, sound lexer 0 |
| B5 | `eval-scripts/run_buffered.py` | sweeps the buffered policy over k |
| B6 | `eval-scripts/run_buffered_alloc.py` | operability: zero false rejects when the allocation respects the buffer |
| B7 | `eval-scripts/run_qcec.py` | external equivalence checker, for capability context only |

To run one alone, set the two paths the scripts read:

```bash
export ARTIFACT_ROOT="$PWD" QASMBENCH_SMALL=/path/to/QASMBench/small
export AXIS2_OUT="$PWD/artifact-run/axis2-out" FUZZ_OUT="$PWD/artifact-run/fuzz-out"
.venv/bin/python harness/eval-scripts/run_optlevel.py
```

B1 must run before B2, B3, B5 and B6. B3 must run before B4.

The fresh outputs of B2 and B4 are byte-identical to the committed
`harness/eval-scripts/e5_results.json` and `fuzz_results.json`. B5 differs only
in its wall-clock fields.

---

## Tier C — recovering the IBM job records

Needs `apikey.json`. Read-only: it retrieves jobs that already ran and consumes
no QPU time.

```bash
.venv/bin/python harness/ibm-hardware/collect_provenance.py --counts
.venv/bin/python harness/ibm-hardware/reconcile_provenance.py
```

The first walks your IBM job history and records id, backend, status, creation
time, shot count, circuit count, and the raw per-circuit bitstring counts. The
second recomputes every published cell from them. `harness/ibm-hardware/PROVENANCE.md`
explains why this exists and lists the campaign job by job.

---

## Tier D — measuring again on real hardware

```bash
bash run_artifact.sh --submit-qpu
```

**This spends about 8 minutes of metered QPU time.** The IBM open plan grants 10
minutes per month. The script prints a warning and waits 15 seconds before it
starts.

It also copies `harness/ibm-hardware/*.json` and `*.md` to
`artifact-run/shipped-backup/` first, because the submission scripts overwrite
`sweep_prereg.json` and the result files. Those hold the pre-registration and the
measurements the paper reports. Git also holds them:
`git checkout -- harness/ibm-hardware` restores them.

| stage | script | what it does |
|---|---|---|
| D1 | `connect_ibm.py` | checks the connection and lists backends |
| D2, D3 | `submit_ibm.py`, `wait_ibm.py` | the distance-resolved leak job, then its analysis |
| D4, D5 | `submit_control.py`, `wait_ctrl.py` | the mechanism control, then its analysis |
| D6, D7 | `submit_sweep.py`, `collect_sweep.py` | the 8-pair sweep across two devices |
| D8, D9 | `submit_repeat.py`, `collect_repeat.py` | the second-snapshot replication |

`submit_repeat.py` reads its pairs verbatim from `sweep_prereg.json` and
deliberately does not re-select them. Replication means the same pairs on a
different calibration snapshot.

---

## Where results live

| directory | contents |
|---|---|
| `artifact-run/` | everything a new run produces; gitignored |
| `harness/axis2-results/` | committed results of the benchmark run |
| `harness/devices/` | the device corpus and its metadata |
| `harness/sim/` | simulator results and blind-prediction scores |
| `harness/ibm-hardware/` | measurements, pre-registrations, and job provenance |

Each results directory carries a `.md` file that reports the numbers and states
the limits of that run.
