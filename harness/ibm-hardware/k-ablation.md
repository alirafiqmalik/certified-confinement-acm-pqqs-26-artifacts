# E4 — Buffer-radius k ablation (isolation vs usable area)

**Derivation order. This framing is MANDATORY for the paper.** We fixed k=1 on **2026-07-23**,
which is the file mtime of `QpuCompiler/Buffer.lean`. Two things motivated it: the documented
nearest-neighbour ZZ threat model (NDSS'25, SWAP'25), and the finding by the reviewer that
support-only confinement misses adjacency. Both came **before** the 2026-07-28 hardware run.

The E1 sweep found a leak at d=1 and a null at d≥2, on 8 of 8 pairs. That result is **consistent
with k=1, and it motivates k=1**. It does **not** "predict" k=1. We did not tune the buffer
against the ΔP data.

## The tradeoff on the real `ibm_marrakesh` patch (`Coupling 12`, co-tenant `F={3}`)
`#eval ((List.range 12).filter (bufferK heronMarrakesh Fd1 k)).length` (kernel-checked defs):

| k (hops) | sterilized qubits | usable qubits (of 12) | usable fraction |
|---|---|---|---|
| 0 (F only) | 1 | 11 | 92% |
| **1** | **4** | **8** | **67%** |
| 2 | 7 | 5 | 42% |
| 3 | 9 | 3 | 25% |
| 4 | 11 | 1 | 8% |

## Reading
- **k=1 is the principled minimum.** It is exactly the buffer that removes the shared coupling
  edge which carries the measured nearest-neighbour ZZ leak. It costs only the 1-hop
  neighbourhood, which is 4 of 12 qubits here.

- **Larger k trades away usable device area fast** — a 4-hop buffer sterilizes all but one qubit
  of this patch. The E1 sweep found **no leak beyond d=1 on any of 8 pairs**, so k=1 is sufficient. On this
  hardware, k>1 over-provisions.

- If a future device or pair shows a leak at d≥2, raise k with the same `bufferK` control. That
  needs no new soundness proof. It is one more decidable region argument to
  `certifySecurity_sound`.
