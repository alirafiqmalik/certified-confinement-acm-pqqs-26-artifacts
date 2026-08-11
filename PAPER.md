# Connections to the paper

Where each claim, symbol, and number of the paper lives in this repository.

---

## 1. Terminology

The paper and the code use the same names. A few need a note.

| paper term | meaning here |
|---|---|
| **validator** | the tenant-side decision procedure. `certifySecurity` in `QpuCompiler/Confine.lean`. |
| **certificate** | the record a call returns: `hardwareLegal`, `policyConfined`, `accepted`. |
| **validation mode** | a guarantee about *any* emitted circuit. The main result. |
| **construction mode** | a guarantee about our own route-and-optimize pipeline. A supporting result. |
| **support confinement** | no non-identity gate of the circuit touches the forbidden region. `confinedb`. |
| **buffered confinement** | the same, over the region grown by `k` hops. `bufferK`, and `bufferF` at k=1. |
| **forbidden region `F`** | the qubits the tenant declares off limits. Tenant-declared. |
| **allowed region `A`** | the tenant's own allocation. The validator is parameterized by `F`, and a tenant that trusts only its allocation sets `F := ¬A`. |
| **patch** | a small hand-encoded device model, as opposed to the 11 real topologies. |
| **direct contact** | a gate that lands *on* a forbidden qubit. The `.cz 0 3` case. |
| **legal-but-adjacent (W1)** | a gate that lands *next to* one. Support confinement accepts it; buffered confinement rejects it. |

Two names are historical and do not mean what they look like:

- **`heavyHex`** is a 12-node **cycle**, every node of degree 2. It is not the
  heavy-hex device family. `heavyHexFrag` is the genuine degree-3 fragment.
- **`checkerSteps`** counts gate traversals. The tool it counts for is the
  validator.

---

## 2. The five evaluation questions

| question | what it asks | where in this repo | how to run it |
|---|---|---|---|
| **E1** | how often does realistic transpiler output violate the policy? | `harness/axis2-results/`, `harness/fuzz-results.md`, `QpuCompiler/EvalWitnesses.lean`, `QpuCompiler/AdvWitnesses.lean` | stages B1–B4, B6 |
| **E2** | is the validator practical? | `harness/Timing.lean`, `harness/TimingBuffered.lean`, `harness/eval-scripts/timing_buffered.csv` | stages A6, B5 |
| **E3** | does validation scale across devices? | `harness/devices/`, `QpuCompiler/DeviceCorpus.lean`, `QpuCompiler/DeviceLib.lean` | stage A4 |
| **E4** | is the chosen policy physically motivated? | `harness/ibm-hardware/`, `QpuCompiler/HeronMarrakesh.lean` | stage A9 offline, tiers C and D live |
| **E5** | what does the buffer cost, and can a tenant apply it? | `harness/ibm-hardware/k-ablation.md`, `harness/axis2-results/RESULTS-BUFFERED.md`, `harness/sim/BLIND-EMULATION.md` | stages B5, B6, A7 (T9) |

Some file and directory names keep an older internal numbering that does **not**
match the paper's E1–E5. Every heading inside those files now states the paper
question. The names that survive:

| name | paper question |
|---|---|
| `harness/axis2-results/` | E1 and E5 |
| `harness/eval-scripts/run_e5b.py`, `e5_results.json` | E1, the violation rates |
| `harness/transpile_axis2.py` | E1 |
| `harness/eval-scripts/timing_e2c.lean` | E2 |

---

## 3. Theorems

| paper | symbol | file | axiom base |
|---|---|---|---|
| Theorem 1, soundness | `certifySecurity_sound` | `QpuCompiler/Confine.lean` | `[propext]` |
| set-level reading | `confinedb_avoids` | `QpuCompiler/Confine.lean` | `[propext]` |
| Theorem 2, cost | `checkerSteps_seq` | `QpuCompiler/Frontend.lean` | no axioms |

Stage A2 prints these. The soundness theorem is quantified over the circuit and
over the region: buffered confinement is that same theorem instantiated at
`bufferK g F k`, not a second result.

---

## 4. Claim to file to symbol

### Validation mode — the main result

| claim | file | symbol |
|---|---|---|
| one validator call over arbitrary output | `QpuCompiler/Confine.lean` | `certifySecurity`, `CertResult` |
| soundness of the certificate | `QpuCompiler/Confine.lean` | `certifySecurity_sound`, `confinedb_avoids` |
| hardware legality | `QpuCompiler/Hardware.lean` | `HWF` |
| support confinement | `QpuCompiler/Confine.lean` | `confinedb`, `conf_ofList`, `conf_toList` |
| routability, checkable before submission | `QpuCompiler/Confine.lean` | `routableb` |
| buffered confinement policy | `QpuCompiler/Buffer.lean` | `bufferK`, `bufferF` |
| precomputed buffered region | `QpuCompiler/Buffer.lean` | `bufferArr`, `bufferArrK`, `bufferMemo` |
| precomputed form is verdict-identical | `QpuCompiler/Buffer.lean` | `certifySecurity_bufferMemo`, `certifySecurity_bufferArrK` |
| cost is one traversal of the gate list | `QpuCompiler/Frontend.lean` | `checkerSteps`, `checkerSteps_seq` |
| untrusted QASM ingestion, sound | `QpuCompiler/Frontend.lean` | `parseQASMSafe` |
| untrusted QASM ingestion, the unsound counterexample | `QpuCompiler/Frontend.lean` | `parseQASM` |
| generic device encoding | `QpuCompiler/DeviceLib.lean` | `EdgeSpec`, `EdgeSpec.toCoupling` |
| 11 real topologies | `QpuCompiler/DeviceCorpus.lean` | `dev_*`, `F_*`, `adj_*`, `far_*` |

### Construction mode — the supporting result

| claim | file | symbol |
|---|---|---|
| routing equals the source up to global phase | `QpuCompiler/CompileHH.lean`, `QpuCompiler/RouteEdge.lean` | `route_hh_congPhase`, `routeEdge_congPhase` |
| routed circuit is hardware-legal | `QpuCompiler/CompileHH.lean` | `route_hh_HWF`, `findPath_valid` |
| routing preserves confinement | `QpuCompiler/Confine.lean` | `route_hh_confine`, `routeEdge_confined`, `swapEdgeNet_confined` |
| optimization preserves confinement | `QpuCompiler/Confine.lean`, `QpuCompiler/Optimize.lean` | `optimize_conf`, `optFix`, `optAdj` |
| the whole pipeline preserves confinement | `QpuCompiler/Confine.lean` | `compile_hh_confine_correct` |
| the buffered form of the same | `QpuCompiler/Buffer.lean` | `compile_hh_confine_buffered`, `compile_hh_confine_bufferedK`, `certify_compile_hh_buffered` |
| the permutation machinery routing rests on | `QpuCompiler/Route.lean`, `QpuCompiler/Swap.lean` | `permDenote`, `bitSwap` |
| equality up to global phase | `QpuCompiler/Equiv.lean` | `CongPhase` |

The 2ⁿ denotation lives in `QpuCompiler/Denote.lean` and `QpuCompiler/KronPow.lean`.
It is ground truth for the bounded equivalence results only. The security path
never calls it.

### Witnesses

| paper row | file | symbol |
|---|---|---|
| direct contact (`.cz 0 3`) | `QpuCompiler/Confine.lean` | `heavyHexFrag`, `fragF`, examples at the file end |
| SWAP drags a secret out | `QpuCompiler/EvalWitnesses.lean` | `wA` |
| optimizer crosses the boundary | `QpuCompiler/EvalWitnesses.lean` | `wB`, `wBsrc` |
| confined positive, no false alarm | `QpuCompiler/EvalWitnesses.lean` | `wC` |
| W1 legal-but-adjacent | `QpuCompiler/AdvWitnesses.lean` | `w1` |
| W2 lexer evasion | `QpuCompiler/AdvWitnesses.lean` | `w2full`, `w2skipped` |
| the bridge to the measured leak | `QpuCompiler/HeronMarrakesh.lean` | `heronMarrakesh`, `Fd1`, `Ffar`, `victimCirc` |

---

## 5. Numbers

Every figure below is regenerated by `run_artifact.sh` or committed as a result
file.

### E1 — violation rates and the front end

| paper | value | where |
|---|---|---|
| violation rate by optimization level | 18 / 53 / 71 / 71 % | `harness/eval-scripts/e5_results.json`, stage B2 |
| circuits per level | n = 38 | same |
| every violating circuit is hardware-legal | yes | same |
| buffer operability, false rejects | 0 at every k and every level | `harness/eval-scripts/buffered_alloc_results.json`, stage B6 |
| circuits that fit as k grows | 31 → 23 → 6 → 0 | same |
| fuzz corpus | 1120 mutants, seed 7 | `harness/eval-scripts/fuzz_results.json`, stage B4 |
| unsound accepts, old lexer | 269 | same |
| unsound accepts, sound lexer | 0 | same |

### E2 — cost

| paper | value | where |
|---|---|---|
| `checkerSteps` on an n-gate line circuit | exactly n+1 | stage A6 |
| plain check at 10⁴ gates | about 6 ms | `harness/eval-scripts/timing_buffered.csv` |
| naive buffered check at k=1 | about 0.9 s | same |
| naive buffered check at k=2 | about 140 s | same |
| memoized buffered check | within noise of the plain check, flat in k | same |

### E3 — device corpus

| paper | value | where |
|---|---|---|
| devices | 11, from 7 to 156 qubits | `harness/devices/corpus_meta.json` |
| topology families | linear/T, heavy-hex, square lattice | `harness/devices/DEVICE-CORPUS.md` |
| kernel-checked verdicts | 44 | stage A4 |
| kernel-checked encoding obligations | 22 | `QpuCompiler/DeviceCorpus.lean` |
| the 156-qubit module | checks in about 5 s | stage A4 |

### E4 — hardware

| paper | value | where |
|---|---|---|
| core run, d=1 | ΔP = 0.397, z = 86 | `harness/ibm-hardware/ibm_results.json` |
| core run, d ≥ 2 | ΔP ≤ 0.0031, no signal | same |
| static-state control | ΔP = 0.380, z = 82 | `harness/ibm-hardware/ibm_ctrl_results.json` |
| pure-drive control | ΔP = 0.006, z = 1.6, null | same |
| pre-registered leak threshold | z ≥ 5 | `harness/ibm-hardware/REPEAT-PREREG.md` |
| campaign totals | 23 pair-observations, 13 pairs, 2 devices, 4 calibrations | `harness/ibm-hardware/REPEAT-RESULTS.md` |
| leaks at d=1 / d ≥ 2 | 22 / 0 | same |
| shots to resolve one bit at d=1 | 60 to 4526, median 186 | `harness/ibm-hardware/PROVENANCE.md`, stage A9 |
| shots to resolve one bit at d ≥ 2 | 1.3×10⁵ to 1.9×10⁷ | same |
| cells that reproduce from raw counts | 16 of 16 | stage A9 |
| arms that returned no data | 2, both cancelled, both disclosed | `harness/ibm-hardware/PROVENANCE.md` |

### E5 — buffer cost and public-data reconstruction

| paper | value | where |
|---|---|---|
| k-ablation on the 12-qubit patch | k=1 → 67 % usable, k=2 → 42 %, k=3 → 25 %, k=4 → 8 % | `harness/ibm-hardware/k-ablation.md` |
| blind prediction, verdicts scored | 46 | `harness/sim/blind_score.json`, stage A7 test T9 |
| true positives / true negatives | 22 / 23 | same |
| false positives / false negatives | 1 / 0 | same |

Simulator closure over all 13 pairs is ΔP ≤ 0.011, in `harness/sim/RESULTS-SIM.md`
and stage A7 test T3.

---

## 6. What the artifact does not reproduce

**The E1 violation rates need QASMBench.** It is an external suite and this
artifact does not vendor it. `run_artifact.sh --fetch-benchmarks` clones it.

**Live hardware costs metered QPU time.** The measurements are committed, and
stage A9 recomputes all of them from raw counts with no account. Only
`--submit-qpu` measures again, and it needs about 8 minutes of an IBM open-plan
allowance of 10 minutes per month.

**Some job-side files are not shipped.** `submit_*.py` writes `ibm_job.json`,
`sweep_jobs.json`, and `repeat_jobs.json`. These are by-products of a
submission. `provenance.json` carries the raw counts instead, and
`harness/ibm-hardware/PROVENANCE.md` explains the recovery.

---

## 7. Scope

**The certificate.** `certifySecurity` validates *any* transpiler output in
polynomial time. Functional equivalence is a separate, bounded result: exact for
small circuits and for the routing fragment only. It is never claimed for
arbitrary output at scale, because that problem is QMA-complete.

**Confinement.** Confinement of gate support, not general information-flow
non-interference. Identity gates are exempt, because they denote to `I`. Idle
residency with no gate at all is outside the model, and the measured channel
needs no gate activity.

**Cost.** One traversal per submission holds *under an O(1) edge-membership
assumption*. That assumption is a modelling choice, not a mechanized one: the
edge test on the encoded patch is itself a list scan.

**Hardware.** The certificate proves structural non-adjacency on a coupling
graph. It is not a bound on the magnitude of crosstalk. Every d ≥ 2 zero is a
null at one sensitivity, not proof of absence: one pair read null on one
calibration and leaked at z = 22.4 on the next.

**Emulated co-tenancy.** IBM Quantum runs one job at a time, so victim and probe
are disjoint qubit sets in a single job. This is a faithful proxy for the
physical channel. It does not reproduce a real scheduler.

**The lexer is untrusted.** Its required invariant is *bug implies safe reject*,
established by testing, not by a theorem. `parseQASM` violates it and exists only
as the counterexample.
