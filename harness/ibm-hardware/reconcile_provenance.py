#!/usr/bin/env python3
"""reconcile_provenance.py — recompute the published (dP, z) from raw counts.

`sweep_results.json` and `repeat_results.json` record only derived statistics. The
`sweep_jobs.json` and `repeat_jobs.json` label maps that produced them are not in the
repository. So nothing in the artifact can re-derive them, and a reviewer must take
the two numbers on trust.

The label map is recoverable without the missing file, because `submit_sweep.py` emits
circuits in a fixed nesting:

    for pair in pairs:            # order given by the prereg
        for dist in (d1, d2):
            for vbit in (0, 1):
                for rep in range(REPS):

That is 2*2*REPS = 8 circuits per pair, pair-major. Combined with the pair list in
`sweep_prereg.json` and the raw counts in `provenance.json`, this script can recompute
and check every published cell.

Statistic (from collect_sweep.py):
    p1     = P(probe measures 1)
    dP     = |p1(vbit=1) - p1(vbit=0)|,  averaged over reps within each vbit arm
    se     = sqrt(p0(1-p0)/N + p1(1-p1)/N),  N = shots * reps
    z      = dP / se
    leak   <=> z >= 5      <-- the pre-registered threshold

Usage (from the Artifact/ root):
    python3 harness/ibm-hardware/reconcile_provenance.py \
        --provenance provenance.json --out reconciliation.json
"""
import argparse, json, math, pathlib

BASE = pathlib.Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
ap.add_argument("--provenance", default=str(BASE / "provenance.json"))
ap.add_argument("--out", default=str(BASE / "reconciliation.json"))
args = ap.parse_args()

prov = {r["job_id"]: r for r in json.load(open(args.provenance))}
sweep_prereg = json.load(open(BASE / "sweep_prereg.json"))
REPS = sweep_prereg["reps"]
SHOTS = sweep_prereg["shots"]
N = SHOTS * REPS

# Jobs are identified by backend, n_pubs, and creation time. submit_sweep.py submits
# marrakesh(40), then fez(24), in one run. So a same-minute (40,24) pair is one campaign.
CAMPAIGNS = {
    "sweep":  {"ibm_marrakesh": "d9k297jjf64c739hhu70", "ibm_fez": "d9k2983jf64c739hhu80"},
    "repeat": {"ibm_marrakesh": "d9k5uljjf64c739hn19g", "ibm_fez": "d9k5um0ii2cc73efn7l0"},
}
PUBLISHED = {"sweep": "sweep_results.json", "repeat": "repeat_results.json"}


def p1_of(pub):
    c = pub["counts"] or {}
    t = sum(c.values())
    return (c.get("1", 0) / t) if t else float("nan")


def stat(v0, v1):
    d = abs(v1 - v0)
    se = math.sqrt(v0 * (1 - v0) / N + v1 * (1 - v1) / N)
    return d, (d / se if se > 0 else 0.0)


out = {}
for campaign, backends in CAMPAIGNS.items():
    published = json.load(open(BASE / PUBLISHED[campaign]))
    pub_by_key = {(p["device"], p["pair"]): p for p in published["pairs"]}
    rows = []
    for backend, job_id in backends.items():
        rec = prov.get(job_id)
        if rec is None or "pubs" not in rec:
            rows.append({"device": backend, "error": f"no counts for {job_id}"})
            continue
        pairs = sweep_prereg["devices"][backend]["pairs"]
        pubs = rec["pubs"]
        expected = len(pairs) * 2 * 2 * REPS
        if len(pubs) != expected:
            rows.append({"device": backend, "error":
                         f"{job_id}: {len(pubs)} pubs, expected {expected}"})
            continue
        i = 0
        for pi, pr in enumerate(pairs):
            row = {"device": backend, "pair": pi, "job_id": job_id,
                   "victim": pr["victim"], "d1_qubit": pr["d1"], "d2_qubit": pr["d2"]}
            for dist in ("d1", "d2"):
                arms = {}
                for vbit in (0, 1):
                    reps = [p1_of(pubs[i + r]) for r in range(REPS)]
                    i += REPS
                    arms[vbit] = sum(reps) / len(reps)
                dp, z = stat(arms[0], arms[1])
                # Attack cost: the shots needed to resolve ONE victim bit at 5 sigma.
                # n = 25 * (p0(1-p0) + p1(1-p1)) / dP^2. This number says whether the
                # channel is practical. It is what a reviewer wants to see when asking,
                # "is this an attack or a crosstalk measurement?"
                var = arms[0] * (1 - arms[0]) + arms[1] * (1 - arms[1])
                shots5 = (25 * var / dp ** 2) if dp > 0 else float("inf")
                row[dist] = {"dP": round(dp, 4), "z": round(z, 1),
                             "p1_vbit0": round(arms[0], 5), "p1_vbit1": round(arms[1], 5),
                             "shots_per_arm": N,
                             "shots_for_1bit_at_5sigma": (round(shots5) if math.isfinite(shots5)
                                                          else None)}
            ref = pub_by_key.get((backend, pi))
            if ref:
                row["published"] = {"d1": ref["d1"], "d2": ref["d2"]}
                row["match"] = all(
                    abs(row[d]["dP"] - ref[d]["dP"]) < 5e-4 and abs(row[d]["z"] - ref[d]["z"]) < 0.6
                    for d in ("d1", "d2"))
            row["leak_d1"] = row["d1"]["z"] >= 5
            row["leak_d2"] = row["d2"]["z"] >= 5
            rows.append(row)
    matched = sum(1 for r in rows if r.get("match"))
    checked = sum(1 for r in rows if "match" in r)
    obs = [(d, r[d]) for r in rows if "error" not in r for d in ("d1", "d2")]
    leak_costs = sorted(c["shots_for_1bit_at_5sigma"] for _, c in obs
                        if c["z"] >= 5 and c["shots_for_1bit_at_5sigma"] is not None)
    out[campaign] = {"rows": rows, "matched": matched, "checked": checked,
                     "d1_leaking": sum(1 for d, c in obs if d == "d1" and c["z"] >= 5),
                     "d1_total": sum(1 for d, _ in obs if d == "d1"),
                     "d2_leaking": sum(1 for d, c in obs if d == "d2" and c["z"] >= 5),
                     "d2_total": sum(1 for d, _ in obs if d == "d2"),
                     "shots_1bit_min": leak_costs[0] if leak_costs else None,
                     "shots_1bit_median": leak_costs[len(leak_costs) // 2] if leak_costs else None,
                     "shots_1bit_max": leak_costs[-1] if leak_costs else None}
    print(f"{campaign}: {matched}/{checked} published cells reproduce from raw counts; "
          f"d1 leaking {out[campaign]['d1_leaking']}/{out[campaign]['d1_total']}, "
          f"d2 leaking {out[campaign]['d2_leaking']}/{out[campaign]['d2_total']}; "
          f"1 bit @5sigma: {out[campaign]['shots_1bit_min']}-{out[campaign]['shots_1bit_max']} shots "
          f"(median {out[campaign]['shots_1bit_median']})")
    for r in rows:
        if "error" in r:
            print(f"   ERROR {r}")
        elif not r.get("match", True):
            print(f"   MISMATCH {r['device']} pair{r['pair']}: "
                  f"recomputed d1={r['d1']['dP']}/{r['d1']['z']} d2={r['d2']['dP']}/{r['d2']['z']} "
                  f"vs published {r['published']}")

# The pre-registered arm that produced no data.
out["unreported_arms"] = []
for jid, rec in prov.items():
    if "CANCELLED" in str(rec.get("status", "")).upper():
        out["unreported_arms"].append({
            "job_id": jid, "backend": rec.get("backend"), "status": rec.get("status"),
            "created": rec.get("created"), "n_pubs": rec.get("n_pubs"),
            "shots": rec.get("shots"),
            "note": "submitted but returned no data; excluded from all reported results"})
if out["unreported_arms"]:
    print("\nSubmitted-but-unreported arms (must be disclosed):")
    for a in out["unreported_arms"]:
        print(f"   {a['backend']:<14} {a['job_id']}  {a['status']}  "
              f"pubs={a['n_pubs']} shots={a['shots']}  {a['created']}")

json.dump(out, open(args.out, "w"), indent=1)
print(f"\nwrote {args.out}")
