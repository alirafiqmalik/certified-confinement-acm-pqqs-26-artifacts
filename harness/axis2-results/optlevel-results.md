# E5 (+E8) — Violation-rate vs Qiskit optimization level — certification overhead

> **RE-VERIFIED 2026-07-30.** We re-ran the evaluation after the `qasmStmts` comment-ordering fix
> in `Frontend.lean`. All figures below are UNCHANGED (violation rate 18/53/71/71%, 27/28
> accepted, 0 confinement false rejects). The Qiskit-transpiled corpus contains no `//` comments.
> So the defect never triggered here. The single `REJECT-PARSE` is `shor_n5.qasm`, which holds a
> genuine `if (c==1)` conditioned gate. This is a correct safe reject.

We certified circuits with the SOUND lexer `parseQASMSafe` (§E3). We used the QASMBench-small
fittable subset (≤12 qubits), transpiled to the 12-node ring plus basis subset at each Qiskit
`optimization_level`. Device model: ring `Coupling 12`, tenant A={0..5}, forbidden F={6..11}.

## Violation rate rises with optimization level (unconstrained "stock transpiler" regime)
| opt-level | circuits | confinement violations caught | **violation rate** |
|---|---|---|---|
| 0 | 38 | 7 | **18%** |
| 1 | 38 | 20 | **53%** |
| 2 | 38 | 27 | **71%** |
| 3 | 38 | 27 | **71%** |

**The threat is pervasive and worsens with optimization.** A tenant-unaware transpiler at the
default and aggressive settings (opt 2–3) places ~71% of circuits partly onto forbidden co-tenant
qubits. The certifier catches all of them. Higher optimization spreads the logical circuit across
more physical qubits (better depth and routing, but no tenant awareness). This increases
co-location.

## Confined regime — false-reject rate (sound parser)
| opt-level | confined circuits | accepted | parse-rejected (conservative) | confinement false-rejects |
|---|---|---|---|---|
| 0 | 29 | 27 | 2 | **0** |
| 1–3 | 28 | 27 | 1 | **0** |

**Zero confinement false-rejects.** The 1–2 "parse-rejected" circuits are `shor_n5` (and one other
at opt0). They contain classically-**conditioned gates**. `parseQASMSafe` now *conservatively
rejects* these gates instead of silently skipping them.

This is the correct, sound behavior. It
is also the honest coverage shift, compared with the old parser's headline. The previous "0/28
false-reject, 99.9% parse-coverage" (via the unsound `parseQASM`) becomes **27/28 accepted plus 1
safe parse-rejection** under `parseQASMSafe`. No confined circuit is wrongly rejected on the
confinement check itself.

## E8 — certification overhead
Per-circuit `certifySecurity` runs in **< 1 ms** (E2), compared with Qiskit `transpile` at
~6–45 ms per circuit (opt-dependent). Certification adds **well under ~10%** to per-circuit
compile time. This is negligible. It is consistent with OwlC's ≤6% framing.

(Note: the Lean `--run` harness has a fixed ~60 s native-compile startup. The harness amortizes
this cost across all circuits. It is not a per-circuit cost.)
