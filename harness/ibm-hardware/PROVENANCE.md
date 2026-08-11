# Hardware campaign provenance

Recovered 2026-08-06. This is a read-only retrieval of existing IBM jobs. It uses no QPU time.

The shipped result files recorded derived statistics only. `sweep_results.json` and
`repeat_results.json` store `(dP, z)` per pair with no job id, no shot counts and no
baselines. The `sweep_jobs.json` / `repeat_jobs.json` label maps that produced them are
not in the repository. The artifact cannot re-derive them.

Two scripts close this:

- `collect_provenance.py` — walks the IBM job history and records id, backend, status,
  creation time, shot count, circuit count and raw per-circuit bitstring counts.
  Output: `provenance.json`.
- `reconcile_provenance.py` — recomputes every published cell from those raw counts and
  compares. Output: `reconciliation.json`.

We did not need to recover the missing label map. `submit_sweep.py` emits circuits in
a fixed nesting — pair-major, then `dist` in `(d1, d2)`, then `vbit` in `(0, 1)`, then
`rep` — so 8 circuits per pair. With the pair list from `sweep_prereg.json` and the pub
ordering from the job, every cell is addressable.

## Campaign map

19 jobs. Job ids resolve as follows. The table marks the four job ids already recorded
in result files.

| created (EDT) | backend | job id | pubs | shots | status | role |
|---|---|---|--:|--:|---|---|
| 2026-07-27 22:48 | marrakesh | `d9k1gu3jf64c739hh0p0` | 16 | 8192 | DONE | core (`ibm_results.json`) ✓ |
| 2026-07-27 22:51 | marrakesh | `d9k1i90ii2cc73efhco0` | 24 | 8192 | DONE | control (`ibm_ctrl_results.json`) ✓ |
| 2026-07-27 23:40 | marrakesh | `d9k297jjf64c739hhu70` | 40 | 8192 | DONE | **sweep** |
| 2026-07-27 23:40 | fez | `d9k2983jf64c739hhu80` | 24 | 8192 | DONE | **sweep** |
| 2026-07-28 03:50 | marrakesh | `d9k5uljjf64c739hn19g` | 40 | 8192 | DONE | **repeat** |
| 2026-07-28 03:50 | fez | `d9k5um0ii2cc73efn7l0` | 24 | 8192 | DONE | **repeat** |
| 2026-07-28 17:03 | **kingston** | `d9khid3jf64c739i79jg` | 40 | 8192 | **CANCELLED** | pre-registered, no data |
| 2026-07-28 17:03 | marrakesh | `d9khifrhdfks73cjm760` | 16 | 8192 | DONE | `results_mrk_t3.json` ✓ |
| 2026-07-29 07:52 | marrakesh | `d9kuj2ibr2fc73e7toog` | 40 | 8192 | DONE | `results_mrk_new.json` ✓ |
| 2026-08-03 02:32 | marrakesh | `d9o3c34sfqic73arlk8g` | 16 | 8192 | **CANCELLED** | no data |
| 2026-08-03 20:40–20:41 | fez | 9 jobs | 2 each | **256** | DONE | separate low-shot runs, not part of the pre-registered campaign |

Total shots across the pre-registered 8192-shot campaign jobs: 1,835,008
(1,839,616 including the nine 256-shot fez runs, which are separate low-shot
experiments and not part of the pre-registered campaign). An earlier figure of
1,507,328 here was wrong: it dropped the 40-pub `mrk_new` job that the campaign
does report.

## Reconciliation result

**All 16 published cells reproduce exactly from raw counts** (8 sweep + 8 repeat),
agreeing to 4 decimal places on `dP` and 0.1 on `z`.

```
sweep : 8/8 reproduce; d1 leaking 7/8, d2 leaking 0/8
repeat: 8/8 reproduce; d1 leaking 8/8, d2 leaking 0/8
```

The one non-leaking distance-1 cell is `ibm_fez` pair 0 (victim 50) in the sweep
(`dP = 0.0002`, `z = 0.0`), which leaked on repeat (`dP = 0.1184`, `z = 22.4`). This is
the flip already recorded in `repeat_results.json`.

## The detection threshold is z >= 5

`collect_sweep.py:35` computes `leak_d1 = row["d1"]["z"] >= 5`, and
`REPEAT-PREREG.md:13`, `collect_repeat.py:4` and `wait_ibm.py:55` agree. Anything in
the range `3 <= z < 5` is classed "marginal", not a leak. Any prose stating a
`|z| >= 3` criterion describes a protocol that was never run.

## Attack cost (new)

Shots to resolve one victim bit at 5 sigma, `n = 25 (p0(1-p0) + p1(1-p1)) / dP^2`:

| | distance 1 | distance 2 |
|---|---|---|
| leaking cells | 15 / 16 | 0 / 16 |
| shots for 1 bit | **60 – 4,526** (median 186) | 1.3e5 – 1.9e7 |

Three to five orders of magnitude separate the two distances. This number answers a key
question: is this an attack, or a crosstalk characterization? At distance 1, a co-tenant
resolves a victim bit in a few hundred shots. At distance 2, the same measurement needs
on the order of a million shots. The `k = 1` buffer is the difference between a
practical and an impractical channel.

Standing caveat, unchanged: victim and probe are qubits 0 and 1 of the same
`QuantumCircuit(2,1)`, submitted as one job by one user. This measures the physical ZZ
channel that co-tenancy would expose. It is not a demonstration of one tenant attacking
another, and we support no claim beyond that.

## Arms submitted that returned no data

We must disclose both. If we silently drop arms that produced nothing, pre-registration is
worthless.

| backend | job id | submitted | pubs | shots | status |
|---|---|---|--:|--:|---|
| `ibm_kingston` | `d9khid3jf64c739i79jg` | 2026-07-28 17:03:48 | 40 | 8192 | CANCELLED |
| `ibm_marrakesh` | `d9o3c34sfqic73arlk8g` | 2026-08-03 02:32:44 | 16 | 8192 | CANCELLED |

The kingston arm is the one pre-registered in `prereg_kingston.json` (5 pairs,
calibration-only outcome-independent selection). We submitted the full 40 circuits at 8192
shots, and the job was cancelled before it returned results. This is why no
`results_kingston.json` exists. We pre-registered a third device, and it yielded no data.
That is the correct disclosure, not silence.

This also means the campaign covers **two** Heron r2 devices (marrakesh, fez), which is
what the paper claims. We attempted a third.

## Reproduce

```bash
python3 harness/ibm-hardware/collect_provenance.py --counts   # needs apikey.json
python3 harness/ibm-hardware/reconcile_provenance.py
```
