# Axis-2 under the BUFFERED confinement policy

Status: **current**. Generated 2026-08-06 with qiskit 2.5.1, Lean 4.31.0, Lake 5.0.0.

This file closes a gap in the earlier axis-2 runs. `run_e5b.py` certifies against the
bare forbidden region `tenantF`, so the headline evaluation never exercised the
*buffered* (k-hop) policy that the paper advocates. Three experiments below.

Reproduce (from the Artifact/ root, after `lake build`):

```bash
export QASMBENCH_SMALL=/path/to/QASMBench/small     # external, not shipped
export AXIS2_OUT=/path/to/scratch/axis2-out
python3 harness/eval-scripts/run_optlevel.py        # transpile corpus
python3 harness/eval-scripts/run_e5b.py             # baseline (unbuffered)
python3 harness/eval-scripts/run_buffered.py        # E-B1
python3 harness/eval-scripts/run_buffered_alloc.py  # E-B2
lake env lean --run harness/TimingBuffered.lean     # E-B3
```

---

## Baseline reproduction

The unbuffered numbers reproduce **exactly** under a toolchain three minor versions
newer than the one that first produced them (`e5_results.json`), which is worth
stating because axis-2 measures a moving target — Qiskit's own transpiler.

| opt | n (full) | violations | rate |
|----:|---------:|-----------:|-----:|
| 0 | 38 | 7 | 18% |
| 1 | 38 | 20 | 53% |
| 2 | 38 | 27 | 71% |
| 3 | 38 | 27 | 71% |

Corpus population also reproduces exactly: full = 38 at every level; confined =
29/28/28/28.

---

## E-B1 — the buffered policy on the existing corpus

`run_buffered.py` -> `buffered_results.json`. Device `heavyHex` (12-node ring),
F = {6..11}, tenant A = {0..5}.

| k | blocked region | \|blocked\| | violations (full), opt 0/1/2/3 |
|--:|---|--:|---|
| 0 | {6..11} | 6/12 | 7 / 20 / 27 / 27 |
| 1 | {0, 5, 6..11} | 8/12 | 34 / 34 / 34 / 34 |
| 2 | {0, 1, 4, 5, 6..11} | 10/12 | 34 / 34 / 34 / 34 |
| 3 | all | 12/12 | 34 / 34 / 34 / 34 |

k = 0 reproduces `run_e5b.py` exactly, as it must (`bufferK g F 0 = F`). This is the
end-to-end check that the buffered entry point agrees with the unbuffered one.

**Reading this honestly: the k >= 1 rows are not a finding about the policy.** They
are an artifact of the allocation. Tenant A = {0..5} and the k=1 halo around F both
claim qubits 0 and 5, so on a 12-ring the tenant and its own buffer overlap and almost
every circuit violates by construction. A buffer carved out of the tenant is not a
buffer. E-B2 runs the experiment that this one cannot.

---

## E-B2 — is the buffered policy OPERABLE?

`run_buffered_alloc.py` -> `buffered_alloc_results.json`. The provider reserves the
k-hop halo as a dead zone and allocates the tenant what is left; the transpiler is
handed **only** the induced subgraph on the allowed set (the restricted-coupling-map
discipline that DynQ assumes and does not verify). The certifier then checks whether
the transpiler actually stayed inside it.

| k | allowed qubits | tenant size | circuits that fit | accepted, opt 0/1/2/3 | false rejects |
|--:|---|--:|--:|---|--:|
| 0 | {0,1,2,3,4,5} | 6/12 | 31/38 | 29/31 at every level | **0** |
| 1 | {1,2,3,4} | 4/12 | 23/38 | 23/23 at every level | **0** |
| 2 | {2,3} | 2/12 | 6/38 | 6/6 at every level | **0** |
| 3 | {} | 0/12 | — | ring fully sterilised | — |

**Zero false rejects at every k and every optimization level.** The two non-accepts at
k=0 are `REJECT-PARSE` (the sound lexer refusing an unrecognized support-bearing
token), not confinement rejects.

This is also the first false-reject arm measured on the **same device** as the
violation rates. The earlier "0 false rejects" arm transpiled onto `PATH6` (a 6-node
linear path) over circuits of <= 6 qubits, while the 18/53/71% rates were measured on
the 12-node ring — different device and different circuit population, so the two
columns were never comparable.

**Capacity is the real cost of the buffer, not runtime.** On a degree-2 ring each hop
costs the tenant two qubits, and the benchmark set that still fits collapses
31 -> 23 -> 6 -> 0. k >= 3 is unusable on a 12-ring at this tenant size. On a
degree-3 heavy-hex device the halo grows faster still. The k-knob does not scale, and
the paper should say so rather than presenting k as freely tunable.

---

## E-B3 — cost of the buffered policy at full device size

`harness/TimingBuffered.lean` -> `timing_buffered.csv`. Device `dev_marrakesh`
(n = 156, 176 edges), F = {16, 22, 23}. Accept path (must scan every gate).

Wall-clock, g = 10000 gates (values below are from the shipped
`timing_buffered.csv`; wall-clock at the millisecond level is noisy, so the
memoised/plain ratio wanders across runs — see the note after the table):

| region | wall | vs plain |
|---|---:|---:|
| plain `F_marrakesh` | 5.88 ms | 1.0x |
| `bufferK … 1` (unmemoised) | 858 ms | **146x** |
| `bufferMemo … (bufferArrK … 1)` | 5.67 ms | **~1x** |
| `bufferK … 2` (unmemoised) | 142.2 **s** | **24,180x** |
| `bufferMemo … (bufferArrK … 2)` | 5.71 ms | **~1x** |

**On the memoised ratio.** Across four runs the plain check measured
5.8–11.4 ms, `bufferArrK1` 5.7–9.4 ms, and `bufferArrK2` 5.7–12.9 ms at
g = 10000 — fully overlapping. The memoised buffered check is therefore the
**same cost as the plain check within measurement noise** (observed ratios
0.96x–2.4x); do not report a fixed small-constant overhead, because there
isn't one. What is robust and reproducible: the *naive* buffer is ~150x at
k = 1 and ~24,000x at k = 2, the memoised buffer is one plain check, and the
memoised cost is flat in k.

Memoised, at g = 1000, the buffer depth is essentially free:

| k | 1 | 2 | 3 | 4 | 8 |
|---|--:|--:|--:|--:|--:|
| wall (ms) | 0.556 | 0.637 | 0.596 | 0.583 | 0.592 |

(plain at g = 1000 is 0.580 ms.)

`bufferArrK_ext` proves the memoised region **is** `bufferK g F k` — the same
function, by `funext` — so `certifySecurity_bufferArrK` gives the identical verdict.
Every gap in the table above is representation cost, not a change of policy.

Two things follow, and both belong in the paper:

1. The naive buffered region is not merely slower, it is **unusable** — Θ(n^k) per
   query, 137 seconds for one 10k-gate circuit at k = 2 on a real device size.
2. Tabulated, the buffered policy costs **1.2–2.4x** the unbuffered check and is
   **flat in k**. The Θ(#gates) claim survives for the advocated policy, but only
   because of `bufferArrK`, and the paper must cite that rather than `checkerSteps`.

`checkerSteps` is blind to all of this: it counts gate traversals and never evaluates
the region predicate. It is a gate-traversal count, not a cost model — as
`Buffer.lean:284-311` already states.

---

## What these results change

- The headline policy is now actually evaluated. Previously it was not.
- The false-reject arm is now measured on the same device as the violation rates.
- The buffer's cost is now measured at full device size, and the Θ(#gates) claim is
  scoped to the tabulated region.
- The buffer's real cost is shown to be **tenant capacity**, not runtime: 6 -> 4 -> 2
  -> 0 usable qubits on a 12-ring as k goes 0 -> 1 -> 2 -> 3.
