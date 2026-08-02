# Artifact — Trust-but-Verify the Transpiler (PQQS 2026)

This is a minimal, axiom-clean Lean 4 / Mathlib artifact. It reproduces the
methods and the results of the paper. The paper gives per-instance,
kernel-checked certificates. Each certificate shows that the output of an
**untrusted** quantum-cloud transpiler is hardware-legal and tenant-confined.

Tenant confinement means the secret qubits of a client never share a qubit or
a coupling edge with a co-tenant. The check costs time linear in program
size. It runs on the output of any compiler.

## Quickstart

```bash
# 1. Lean toolchain (skip if you already have elan/lake on PATH)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
export PATH="$HOME/.elan/bin:$PATH"

# 2. Build and kernel-check the Lean library
lake build                                   # expect: Build completed successfully (2381 jobs)

# 3. Python environment for the harness (samples, corpus, simulator)
bash setup.sh
source .venv/bin/activate

# 4. Independently re-verify the 11-device corpus (don't trust `lake build` alone — see below)
bash harness/devices/verify_corpus.sh

# 5. Run the zero-QPU simulator test suite (9 tests, no IBM account needed)
python3 harness/sim/test_e2e.py

# 6. Certify the 4 shipped sample circuits
python3 harness/certify_qasm.py --samples
```

We ran all six steps from start to end to produce this artifact. The section
[Verified output](#verified-output) below gives the expected output for
steps 4–6.

## What this artifact proves (and what it does not)

Proved, machine-checked in the Lean kernel:

- A one-call certifier `certifySecurity`. Its soundness theorem
  `certifySecurity_sound` holds for **arbitrary** transpiler output, and its
  trust base is **`[propext]` only**.
- Routing (SWAP insertion) equals the source up to global phase. The proof
  works **symbolically**, with no 2ⁿ state vector.
- Route-then-optimize never creates a secret-to-co-tenant channel
  (`compile_hh_confine_correct`).
- The security check costs Θ(#gates) (`checkerSteps_seq`, plus measured
  wall-clock).

> ### Honest scope (read this)
>
> **Scope of the certificate.** The security certificate certifies *any*
> output in polynomial time. **Functional equivalence** is a *bounded*
> companion result. It is exact for small circuits and for the routing
> fragment only. We **never** claim it for arbitrary output at scale, because
> that problem is QMA-complete.
>
> **Scope of confinement.** Confinement means support-confinement: no
> co-location on a forbidden qubit. It applies to an allowed region `A` and a
> forbidden region `F`, with secrets `S ⊆ A`. It is **not** general
> information-flow non-interference.
>
> **Device models.** There are five:
>
> - the 12-node heavy-hex ring, `heavyHex : Coupling 12`
> - a degree-3 4-qubit fragment, `heavyHexFrag : Coupling 4`
> - a 14-qubit patch with two degree-3 sites, `heronPatch`
> - the real measured `ibm_marrakesh` neighbourhood, `heronMarrakesh`
> - a corpus of 11 real IBM topologies from 7 to 156 qubits, in
>   `DeviceCorpus.lean`.
>
> **The OpenQASM lexer.** It covers the basis subset `{x, sx, id, rz, cz/cx}`.
> It is **untrusted**. Use `parseQASMSafe`, which rejects any statement it
> cannot account for. Do **not** use `parseQASM` for anything except the
> counterexample below. It silently drops unrecognized statements. A fuzz
> pass turned 269 of 1120 crafted inputs into false accepts through that
> hole. Either lexer's guarantee rests on `certifySecurity_sound` over the
> resulting circuit.
>
> **Real-hardware claims.** The certificate proves *structural*
> non-adjacency on a coupling graph. It is not a bound on crosstalk
> magnitude. The bridge to a measured leak (`HeronMarrakesh.lean`,
> `harness/ibm-hardware/`) is a single device, a single victim, and a small
> set of calibration snapshots. See `harness/ibm-hardware/IBM-RESULTS.md` and
> `SWEEP-RESULTS.md` for the exact count and the honesty notes.

## Directory layout

```
Artifact/
├── setup.sh                 # creates a Python venv with everything the harness needs
├── lakefile.toml, lean-toolchain, lake-manifest.json
├── QpuCompiler.lean          # library root — imports every module below
├── QpuCompiler/               # the proved Lean 4 / Mathlib library (22 files)
└── harness/
    ├── CertifyQASM.lean, CertifyQASMSafe.lean, Timing.lean   # Lean side of the harness
    ├── certify_qasm.py, transpile_axis2.py                   # Python driver + real-circuit ingestion
    ├── samples/               # 4 hand-written QASM circuits with known verdicts
    ├── devices/                # 11-device corpus generator + independent re-verifier
    ├── eval-scripts/           # fuzzing, opt-level sweep, QCEC comparison
    ├── axis2-results/          # real-benchmark coverage run (QASMBench, transpiled)
    ├── sim/                     # zero-QPU forward model + 9-test pre-flight suite + blind prediction
    └── ibm-hardware/            # real IBM Heron r2 submission/collection scripts + measured results
```

## Where each paper claim lives (claim → file : symbol)

| Paper claim | File | Symbol |
|---|---|---|
| C1 one-call certifier over arbitrary output | `QpuCompiler/Confine.lean` | `certifySecurity`, `certifySecurity_sound` (`[propext]` only) |
| C1 untrusted QASM ingestion | `QpuCompiler/Frontend.lean` | `parseQASMSafe` (sound); `parseQASM` (the unsound counterexample) |
| C2 symbolic routing, equal up to global phase | `QpuCompiler/CompileHH.lean`, `RouteEdge.lean` | `route_hh_congPhase`, `routeEdge_congPhase` |
| C2 routing preserves confinement | `QpuCompiler/Confine.lean` | `route_hh_confine`, `routeEdge_confined` |
| C3 compile-level confinement (route+optimize) | `QpuCompiler/Confine.lean` | `compile_hh_confine_correct`, `optimize_conf` |
| C3 degree-3 "money example" | `QpuCompiler/Confine.lean` | `heavyHexFrag`, `fragF`, examples at file end |
| C3 neighbour-buffered confinement | `QpuCompiler/Buffer.lean` | `bufferF`, `bufferK`, `compile_hh_confine_buffered`, `certify_compile_hh_buffered` |
| C3 O(1) buffered region queries | `QpuCompiler/Buffer.lean` | `bufferArr`, `bufferMemo`, `certifySecurity_bufferMemo` |
| C4 linear cost Θ(#gates) | `QpuCompiler/Frontend.lean` | `checkerSteps`, `checkerSteps_seq` |
| Generic device encoding | `QpuCompiler/DeviceLib.lean` | `EdgeSpec`, `EdgeSpec.toCoupling` |
| Eval Axis-1 caught-violation witnesses | `QpuCompiler/EvalWitnesses.lean` | `wA`, `wB`/`wBsrc`, `wC` |
| Eval hostile-transpiler witnesses | `QpuCompiler/AdvWitnesses.lean` | `w1` (legal-but-adjacent), `w2full`/`w2skipped` (lexer evasion) |
| Bridge to the measured hardware leak | `QpuCompiler/HeronMarrakesh.lean` | `heronMarrakesh`, `Fd1`, `Ffar`, `victimCirc` |
| Eval Axis-2 real-circuit ingestion | `harness/` | `CertifyQASMSafe.lean`, `certify_qasm.py`, `samples/` |
| Eval Axis-3 wall-clock timing | `harness/` | `Timing.lean` |
| Live IBM hardware runs (leak sweep, replication, new pairs) | `harness/ibm-hardware/` | `submit_*.py`, `collect_*.py`, `IBM-RESULTS.md`, `SWEEP-RESULTS.md`, `REPEAT-RESULTS.md` |
| Offline forward model + 9-test end-to-end suite | `harness/sim/` | `qpu_sim.py`, `test_e2e.py`, `tau_discriminator.py`, `RESULTS-SIM.md` |
| **Blind** leak prediction from public metadata + held-out scoring | `harness/sim/` | `blind_predict.py`, `blind_score.py`, `BLIND-EMULATION.md` |
| **Multi-device certifier corpus** (11 real topologies, 7–156q) | `harness/devices/` + `QpuCompiler/{DeviceLib,DeviceCorpus}.lean` | `gen_device_corpus.py`, `verify_corpus.sh`, `DEVICE-CORPUS.md` |

Two harness axes need no IBM account and no QPU quota. `harness/sim/` needs
only `qiskit` and `qiskit-aer`. `harness/devices/` takes its topologies from
`qiskit_ibm_runtime.fake_provider`. Only `harness/ibm-hardware/` spends
metered QPU time and needs a token. See
[Reproducing the real-hardware run](#reproducing-the-real-hardware-run).

## Axiom-cleanliness check

```
lake env lean --run - <<'EOF'
import QpuCompiler
#print axioms QpuCompiler.certifySecurity_sound        -- [propext]
#print axioms QpuCompiler.compile_hh_confine_correct   -- [propext, Classical.choice, Quot.sound]
#print axioms QpuCompiler.compile_hh_confine_buffered  -- [propext, Classical.choice, Quot.sound]
#print axioms QpuCompiler.EdgeSpec.toCoupling          -- [propext, Quot.sound]
#print axioms QpuCompiler.checkerSteps_seq             -- (no axioms)
EOF
```

The tree contains no `native_decide` and no `Lean.ofReduceBool`. Every
`decide` witness reduces in the kernel under the standard three axioms.

## Verified output

We ran the Quickstart commands above end to end against this exact directory
before publication. Expected output:

**`bash harness/devices/verify_corpus.sh`** — independently recomputes all 44
verdicts across all 11 devices outside the generated file, so a code-generation
defect cannot pass silently:

```
ALL 11 DEVICES PASS (44 verdicts recomputed independently)
clean: no sorry / native_decide / ofReduceBool / axiom
```

> **Why not trust `lake build` alone?** Lake replays cached `.olean` files and
> reports success without re-checking a single `decide`. `verify_corpus.sh`
> deletes the build products of the corpus module first. This step forces a
> genuine re-check.

**`python3 harness/sim/test_e2e.py`** — a 9-test, zero-QPU pre-flight suite
that also cross-checks the Python simulator against the Lean-kernel-checked
certifier (test T8):

```
9/9 tests passed
```

This is the recommended stand-in for a live hardware run. It costs no QPU
quota and needs no IBM account. T8 confirms that the Python and Lean halves
agree. It does this by calling `lake env lean` directly, for a real
kernel-checked verdict.

**`python3 harness/certify_qasm.py --samples`**:

```
ACCEPT  harness/samples/01_ok_confined.qasm    (gates=7 legal=true  confined=true)
REJECT  harness/samples/02_cotenant_touch.qasm (gates=3 legal=true  confined=false)
REJECT  harness/samples/03_illegal_edge.qasm   (gates=2 legal=false confined=false)
ACCEPT  harness/samples/04_ok_ring_chain.qasm  (gates=8 legal=true  confined=true)
```

Sample 02 is the "money example". It is a circuit that is perfectly legal on
the hardware graph. The checker rejects it because it places the client's
qubits next to a forbidden co-tenant region. That is the gap that a
hardware-legality check alone cannot see. It is the reason this artifact
exists.

## Reproducing the real-hardware run

`harness/ibm-hardware/` holds the scripts that produced the live-device
numbers in the paper (`IBM-RESULTS.md`, `SWEEP-RESULTS.md`,
`REPEAT-RESULTS.md`, `k-ablation.md`). It also holds the raw result JSON that
these numbers came from. To reproduce a live run, you need your own IBM
Quantum account. Put a token in an `apikey.json` file next to this README.
The scripts' `connect_ibm.py` file shows the format to use. Real device time
is a metered resource. Confirm your remaining allowance before you submit a
job.

We did not re-run these scripts for this artifact. The zero-QPU paths above
(`harness/sim/`, `harness/devices/`) are the reproducible, quota-free
verification path. We ship the already-collected results in
`harness/ibm-hardware/*.json` and `*.md` as-is.
# certified-confinement-acm-pqqs-26-artifacts
