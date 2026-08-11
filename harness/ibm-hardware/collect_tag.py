"""
This is a generic collector for a jobs_<tag>.json submission.

Its statistics are identical to collect_sweep.py and collect_repeat.py. It uses an
unpooled two-proportion (Wald) z-test over N = shots x reps. The leak criterion is
z >= 5.

Usage: collect_tag.py <tag>
This script writes results_<tag>.json. It reads the token at runtime. It never
prints the token.
"""
import json, os, math, pathlib, sys

BASE = str(pathlib.Path(__file__).resolve().parent) + "/"
for _p in pathlib.Path(__file__).resolve().parents:
    if (_p / "apikey.json").exists():
        break
else:
    raise FileNotFoundError("apikey.json not found in any parent directory of this script")
_KEYFILE = json.load(open(_p / "apikey.json"))
KEY = _KEYFILE["apikey"]
# The instance name belongs to the account, not to the experiment.
# Set the IBM_INSTANCE environment variable, or add an "instance" field to apikey.json.
# If both stay unset, the service selects the default instance of the account.
_INSTANCE = os.environ.get("IBM_INSTANCE") or _KEYFILE.get("instance")
_INST = {"instance": _INSTANCE} if _INSTANCE else {}
from qiskit_ibm_runtime import QiskitRuntimeService

tag = sys.argv[1]
info = json.load(open(BASE + f"jobs_{tag}.json"))
svc = QiskitRuntimeService(channel="ibm_quantum_platform", token=KEY, **_INST)
job = svc.job(info["job_id"])
st = str(job.status())
print(f"{tag}: {info['backend']} job {info['job_id']} status={st}")
if "DONE" not in st:
    print("NOT DONE — nothing collected, nothing fabricated."); raise SystemExit(2)

SHOTS = 8192; REPS = 2; N = SHOTS * REPS


def p1(pub):
    d = pub.data; reg = list(d.__dict__.keys())[0]
    c = getattr(d, reg).get_counts(); t = sum(c.values())
    return c.get('1', 0) / t


def tp(a, b, n):
    se = math.sqrt(a * (1 - a) / n + b * (1 - b) / n)
    d = abs(b - a)
    return d, (d / se if se > 0 else 0)


res = job.result()
cells = {}
for lab, pub in zip(info["labels"], res):
    cells.setdefault(lab["pair"], {}).setdefault(lab["dist"], {}).setdefault(lab["vbit"], []).append(p1(pub))

rows = []
for pi in sorted(cells):
    pr = info["pairs"][pi]
    r = {"pair": pi, "victim": pr["victim"], "d1_qubit": pr["d1"], "d2_qubit": pr["d2"]}
    for dist in ("d1", "d2"):
        v0 = sum(cells[pi][dist][0]) / len(cells[pi][dist][0])
        v1 = sum(cells[pi][dist][1]) / len(cells[pi][dist][1])
        dp, z = tp(v0, v1, N)
        r[dist] = {"dP": round(dp, 4), "z": round(z, 1)}
    r["leak_d1"] = r["d1"]["z"] >= 5
    r["leak_d2"] = r["d2"]["z"] >= 5
    rows.append(r)

d1 = sum(x["leak_d1"] for x in rows); d2 = sum(x["leak_d2"] for x in rows)
print(f"\n{'pair':<6}{'victim':<8}{'d=1':<24}{'d>=2':<24}{'verdict'}")
for r in rows:
    v = "HOLDS" if (r["leak_d1"] and not r["leak_d2"]) else ("no-leak@d1" if not r["leak_d1"] else "LEAK@d2!")
    print(f"{r['pair']:<6}{r['victim']:<8}"
          f"{'dP=%s, z=%s' % (r['d1']['dP'], r['d1']['z']):<24}"
          f"{'dP=%s, z=%s' % (r['d2']['dP'], r['d2']['z']):<24}{v}")
print(f"\n{tag}: leak@d1 {d1}/{len(rows)} · leak@d2 {d2}/{len(rows)}")
print(f"certifier soundness (never accepts a leaking placement) = {len(rows)-d2}/{len(rows)}")

json.dump({"tag": tag, "backend": info["backend"], "job_id": info["job_id"],
           "pair_origin": info.get("pair_origin"), "last_calibration": info.get("last_calibration"),
           "calibration_snapshot": info.get("calibration_snapshot"),
           "submitted_utc": info.get("submitted_utc"),
           "leak_d1": d1, "leak_d2": d2, "n": len(rows), "pairs": rows},
          open(BASE + f"results_{tag}.json", "w"), indent=1)
print(f"wrote results_{tag}.json")
