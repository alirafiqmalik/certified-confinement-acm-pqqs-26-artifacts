#!/usr/bin/env python3
"""collect_provenance.py — recover per-job provenance for the hardware campaign.

The shipped result files record only derived statistics. `sweep_results.json` and
`repeat_results.json` store (dP, z) per pair. They give no job id, no shot count, and
no baseline. So no downstream process can recompute or audit them.

This script reads the IBM job history. For every job, it writes the id, backend,
status, creation time, program, shot count, and circuit count. Where the job returned
data, it also writes the raw per-circuit bitstring counts.

This script is read-only. It retrieves existing jobs and uses no QPU time.

Usage (from the Artifact/ root):
    python3 harness/ibm-hardware/collect_provenance.py [--limit 200] [--out provenance.json]
"""
import argparse, json, pathlib, sys
from qiskit_ibm_runtime import QiskitRuntimeService

ap = argparse.ArgumentParser()
ap.add_argument("--limit", type=int, default=200)
ap.add_argument("--key", default=None, help="path to apikey.json (default: search parents)")
ap.add_argument("--out", default=str(pathlib.Path(__file__).parent / "provenance.json"))
ap.add_argument("--counts", action="store_true", help="also pull raw bitstring counts")
args = ap.parse_args()

if args.key:
    keypath = pathlib.Path(args.key)
else:
    for _p in pathlib.Path(__file__).resolve().parents:
        if (_p / "apikey.json").exists():
            keypath = _p / "apikey.json"
            break
    else:
        sys.exit("apikey.json not found in any parent directory")
KEY = json.load(open(keypath))["apikey"]

svc = None
for ch in ("ibm_quantum_platform", "ibm_cloud", "ibm_quantum"):
    try:
        svc = QiskitRuntimeService(channel=ch, token=KEY)
        break
    except Exception as e:
        print(f"  channel {ch} failed: {type(e).__name__}: {str(e)[:100]}", file=sys.stderr)
if svc is None:
    sys.exit("could not connect on any channel")

jobs = svc.jobs(limit=args.limit)
print(f"# {len(jobs)} jobs visible", file=sys.stderr)

recs = []
for j in jobs:
    rec = {"job_id": j.job_id()}
    for field, fn in (
        ("backend", lambda: j.backend().name),
        ("status", lambda: str(j.status())),
        ("created", lambda: str(j.creation_date)),
        ("program", lambda: getattr(j, "primitive_id", None) or getattr(j, "program_id", None)),
        ("tags", lambda: list(j.tags) if getattr(j, "tags", None) else []),
        ("usage_s", lambda: j.usage_estimation),
    ):
        try:
            rec[field] = fn()
        except Exception as e:
            rec[field] = f"ERR {type(e).__name__}"

    # The inputs carry the pre-registered protocol parameters: shot count and circuit count.
    try:
        inp = j.inputs or {}
        pubs = inp.get("pubs") or []
        rec["n_pubs"] = len(pubs)
        opts = inp.get("options") or {}
        rec["shots"] = inp.get("shots") or opts.get("default_shots") or (
            pubs[0][2] if pubs and len(pubs[0]) > 2 else None)
    except Exception as e:
        rec["inputs_err"] = f"{type(e).__name__}: {str(e)[:80]}"

    if args.counts and rec.get("status", "").upper().find("DONE") >= 0:
        try:
            res = j.result()
            per = []
            for pub in res:
                d = pub.data
                field = next(iter(d.__dict__)) if hasattr(d, "__dict__") else None
                arr = getattr(d, field) if field else None
                per.append({"creg": field,
                            "num_shots": int(getattr(arr, "num_shots", 0) or 0),
                            "counts": getattr(arr, "get_counts", lambda: None)()})
            rec["pubs"] = per
        except Exception as e:
            rec["result_err"] = f"{type(e).__name__}: {str(e)[:120]}"
    recs.append(rec)
    print(f"  {rec['job_id']}  {rec.get('backend'):<16} {rec.get('status'):<24} "
          f"pubs={rec.get('n_pubs')} shots={rec.get('shots')}", file=sys.stderr)

json.dump(recs, open(args.out, "w"), indent=1)
print(f"\nwrote {args.out} ({len(recs)} jobs)", file=sys.stderr)
