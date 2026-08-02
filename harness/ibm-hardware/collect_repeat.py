"""
E1-R collector — second-snapshot replication. The statistics match `collect_sweep.py`
exactly: an unpooled two-proportion Wald z-test over N = shots x reps, with a leak
criterion of z >= 5. So snapshot 1 and snapshot 2 are compared on exactly the same
rule. This script also emits a per-pair side-by-side comparison against the first
snapshot. It reports pairs that FLIPPED in either direction.
"""
import json, math, pathlib, sys, time

BASE = str(pathlib.Path(__file__).resolve().parent) + "/"
for _p in pathlib.Path(__file__).resolve().parents:
    if (_p / "apikey.json").exists():
        break
else:
    raise FileNotFoundError("apikey.json not found in any parent directory of this script")
KEY = json.load(open(_p / "apikey.json"))["apikey"]
from qiskit_ibm_runtime import QiskitRuntimeService

jobs = json.load(open(BASE + "repeat_jobs.json"))
prereg = json.load(open(BASE + "sweep_prereg.json"))
svc = QiskitRuntimeService(channel="ibm_quantum_platform", token=KEY, instance="qos-instance")

WAIT = "--wait" in sys.argv
while True:
    sts = {}
    for name, info in jobs["devices"].items():
        sts[name] = str(svc.job(info["job_id"]).status())
    print({k: v for k, v in sts.items()}, flush=True)
    if all("DONE" in v for v in sts.values()):
        break
    if any(("ERROR" in v or "CANCELLED" in v) for v in sts.values()):
        print("JOB FAILED — aborting, nothing fabricated."); raise SystemExit(1)
    if not WAIT:
        print("NOT_ALL_DONE (re-run with --wait to block)"); raise SystemExit(2)
    time.sleep(30)


def p1(pub):
    d = pub.data; reg = list(d.__dict__.keys())[0]
    c = getattr(d, reg).get_counts(); t = sum(c.values())
    return c.get('1', 0) / t


def tp(a, b, n):
    se = math.sqrt(a * (1 - a) / n + b * (1 - b) / n)
    d = abs(b - a)
    return d, (d / se if se > 0 else 0)


SHOTS = prereg["shots"]; N = SHOTS * prereg["reps"]
allpairs = []; agree = 0
for name, info in jobs["devices"].items():
    res = svc.job(info["job_id"]).result(); labels = info["labels"]
    cells = {}
    for lab, pub in zip(labels, res):
        cells.setdefault(lab["pair"], {}).setdefault(lab["dist"], {}).setdefault(lab["vbit"], []).append(p1(pub))
    for pi in sorted(cells):
        row = {"device": name, "pair": pi}
        for dist in ("d1", "d2"):
            v0 = sum(cells[pi][dist][0]) / len(cells[pi][dist][0])
            v1 = sum(cells[pi][dist][1]) / len(cells[pi][dist][1])
            dp, z = tp(v0, v1, N)
            row[dist] = {"dP": round(dp, 4), "z": round(z, 1)}
        leak_d1 = row["d1"]["z"] >= 5; leak_d2 = row["d2"]["z"] >= 5
        row["leak_d1"] = bool(leak_d1); row["leak_d2"] = bool(leak_d2)
        row["prediction_holds"] = bool(leak_d1 and not leak_d2)
        if row["prediction_holds"]: agree += 1
        allpairs.append(row)

# --- side-by-side vs snapshot 1 ---
try:
    old = {(p["device"], p["pair"]): p for p in json.load(open(BASE + "sweep_results.json"))["pairs"]}
except Exception:
    old = {}

print(f"\n=== SNAPSHOT 2: {len(allpairs)} pairs; leak@d1 & null@d2 holds on {agree}/{len(allpairs)} ===")
print(f"{'device':<15}{'pair':<6}{'snap1 d1':<20}{'snap2 d1':<20}{'snap2 d2':<18}{'verdict'}")
flips = []
for r in allpairs:
    o = old.get((r["device"], r["pair"]))
    o1 = f"dP={o['d1']['dP']},z={o['d1']['z']}" if o else "n/a"
    n1 = f"dP={r['d1']['dP']},z={r['d1']['z']}"
    n2 = f"dP={r['d2']['dP']},z={r['d2']['z']}"
    v = "HOLDS" if r["prediction_holds"] else ("no-leak@d1" if not r["leak_d1"] else "LEAK@d2!")
    if o is not None:
        o_leak1 = o["d1"]["z"] >= 5
        if o_leak1 != r["leak_d1"]:
            flips.append((r["device"], r["pair"], o_leak1, r["leak_d1"]))
    print(f"{r['device'][:14]:<15}{r['pair']:<6}{o1:<20}{n1:<20}{n2:<18}{v}")

d1_leaks = sum(1 for r in allpairs if r["leak_d1"])
d2_leaks = sum(1 for r in allpairs if r["leak_d2"])
print(f"\nsnapshot-2 totals: leak@d1 {d1_leaks}/{len(allpairs)} · leak@d2 {d2_leaks}/{len(allpairs)}")
print(f"certifier soundness (never accepts a leaking placement) = {len(allpairs)-d2_leaks}/{len(allpairs)} "
      f"[a d>=2 leak would be the only way to break it]")
if flips:
    print("\nPAIRS THAT FLIPPED d1 leak-status between snapshots (report these, do not hide them):")
    for dev, pi, a, b in flips:
        print(f"  {dev} pair{pi}: snap1 leak={a} -> snap2 leak={b}")
else:
    print("\nno pair flipped d1 leak-status between snapshots")

json.dump({"agree": agree, "total": len(allpairs), "d1_leaks": d1_leaks, "d2_leaks": d2_leaks,
           "flips": flips, "pairs": allpairs,
           "calibration": {k: {"last_calibration": v.get("last_calibration"),
                               "snapshot": v.get("calibration_snapshot")}
                           for k, v in jobs["devices"].items()},
           "submitted_utc": jobs.get("submitted_utc")},
          open(BASE + "repeat_results.json", "w"), indent=1)
print("\nwrote repeat_results.json")
