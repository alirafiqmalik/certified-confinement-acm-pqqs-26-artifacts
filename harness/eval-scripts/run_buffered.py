#!/usr/bin/env python3
"""run_buffered.py — Axis-2 sweep under the BUFFERED confinement policy.

`run_e5b.py` certifies against the bare forbidden region `tenantF`. This script
certifies the same corpus against the `k`-hop buffered region, for k = 0..K, and
records both the verdicts and the size of the blocked region.

k=0 must reproduce run_e5b.py exactly (`bufferK g F 0 = F`); the script asserts it.

Usage (from the Artifact/ root, after `lake build` and run_optlevel.py):
    AXIS2_OUT=/path/to/axis2-out python3 harness/eval-scripts/run_buffered.py [--kmax 3]
"""
import glob, subprocess, os, pathlib, re, json, argparse, time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = os.environ.get("ARTIFACT_ROOT", str(HERE.parents[1]))
ENTRY = "harness/CertifyQASMBuffered.lean"
OPT = os.environ.get("AXIS2_OUT", str(HERE.parent / "axis2-out"))
LAKE = os.path.expanduser("~/.elan/bin/lake")
LEAN = os.path.expanduser("~/.elan/bin/lean")
ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ.get("PATH", ""))

ap = argparse.ArgumentParser()
ap.add_argument("--kmax", type=int, default=3)
ap.add_argument("--out", default=str(HERE / "buffered_results.json"))
args = ap.parse_args()

files = []
for opt in (0, 1, 2, 3):
    for regime in ("full", "confined"):
        files += [os.path.relpath(f, ROOT) for f in sorted(glob.glob(f"{OPT}/o{opt}/{regime}/*.qasm"))]
if not files:
    raise SystemExit(f"no QASM under {OPT} — run run_optlevel.py first")

results = {}
for k in range(args.kmax + 1):
    t0 = time.perf_counter()
    r = subprocess.run([LAKE, "env", LEAN, "--run", ENTRY, str(k)] + files,
                       cwd=ROOT, env=ENV, capture_output=True, text=True)
    elapsed = time.perf_counter() - t0
    blocked = None
    m = re.search(r"blocked=\[([^\]]*)\]", r.stdout)
    if m:
        blocked = [int(x) for x in m.group(1).split(",") if x.strip()]
    verds = {}
    for ln in r.stdout.splitlines():
        mm = re.match(r"(ACCEPT|REJECT|REJECT-PARSE)\s+(\S+)", ln)
        if mm:
            verds[mm.group(2)] = (mm.group(1), "confined=false" in ln, "legal=false" in ln)
    summary = {}
    for opt in (0, 1, 2, 3):
        row = {}
        for regime in ("full", "confined"):
            fs = [os.path.relpath(f, ROOT) for f in sorted(glob.glob(f"{OPT}/o{opt}/{regime}/*.qasm"))]
            vs = [verds[f] for f in fs if f in verds]
            n = len(vs)
            if not n:
                continue
            row[regime] = dict(
                n=n,
                accept=sum(1 for v in vs if v[0] == "ACCEPT"),
                reject=sum(1 for v in vs if v[0] == "REJECT"),
                reject_parse=sum(1 for v in vs if v[0] == "REJECT-PARSE"),
                violations=sum(1 for v in vs if v[1]),
            )
        summary[f"opt{opt}"] = row
    results[f"k{k}"] = dict(blocked=blocked, n_blocked=len(blocked) if blocked else None,
                            wall_s=round(elapsed, 2), summary=summary)
    fullrow = {o: summary[o]["full"]["violations"] for o in summary if "full" in summary[o]}
    print(f"k={k}  blocked={len(blocked) if blocked else '?'}/12  "
          f"violations(full) by opt={fullrow}  [{elapsed:.1f}s]")

json.dump(results, open(args.out, "w"), indent=1)
print(f"\nwrote {args.out}")
