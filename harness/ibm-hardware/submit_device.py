"""
Generic leak-sweep submitter for a named Heron r2 device. It has a hard quota guard.

Usage:  submit_device.py <backend> <npairs> <tag> [--reuse-prereg]

 - <backend>       ibm_fez | ibm_marrakesh | ibm_kingston
 - <npairs>        the number of victim/probe triples (victim, d1, d2)
 - <tag>           a label. Artifacts land in jobs_<tag>.json.
 - --reuse-prereg  Reuse pairs from sweep_prereg.json, for replication.
                   Omit this flag for a NEW device. Then the script selects pairs
                   from calibration data only (outcome-independent). It writes
                   them to prereg_<tag>.json.

QUOTA GUARD: this script refuses to submit when the estimated cost exceeds the
remaining free-tier seconds minus RESERVE. The cost model is calibrated on
observed runs, at about 2.7 QPU-seconds per circuit (40 circuits take 106.9 s
on marrakesh, and 24 circuits take 46.9 s on fez).

The script reads the token at runtime. It never prints the token.
"""
import json, os, pathlib, sys, datetime

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

from qiskit import QuantumCircuit, transpile
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2

SEC_PER_CIRCUIT = 2.70
RESERVE = 5.0          # Safety margin. The script never spends the last few seconds of quota.
WIN = 40e-6; SHOTS = 8192; REPS = 2

backend_name = sys.argv[1]; npairs = int(sys.argv[2]); tag = sys.argv[3]
reuse = "--reuse-prereg" in sys.argv

svc = QiskitRuntimeService(channel="ibm_quantum_platform", token=KEY, **_INST)
u = svc.usage(); remaining = u["usage_remaining_seconds"]


def pick_pairs(backend, n):
    """This selection is outcome-independent. It uses calibration data only: readout error and T2."""
    nq = backend.num_qubits; tgt = backend.target
    adj = {i: set() for i in range(nq)}
    for a, b in backend.coupling_map.get_edges():
        adj[a].add(b); adj[b].add(a)
    def rerr(q):
        try: return tgt["measure"][(q,)].error
        except Exception: return 1.0
    def T2(q):
        try: return tgt.qubit_properties[q].t2 or 0
        except Exception: return 0
    used = set()
    # --exclude-measured: skip every qubit that sweep_prereg.json already used for this
    # device. This way, a "new pairs" run adds genuinely independent qubit pairs. It
    # does not re-measure couplers that already have three snapshots.
    if "--exclude-measured" in sys.argv:
        try:
            pre0 = json.load(open(BASE + "sweep_prereg.json"))
            for pr0 in pre0["devices"][backend.name]["pairs"]:
                used |= {pr0["victim"], pr0["d1"], pr0["d2"]}
            print(f"excluding {len(used)} already-measured qubits: {sorted(used)}")
        except Exception as e:
            print("WARN could not load exclusions:", e)
    pairs = []
    for v in sorted((q for q in range(nq) if len(adj[q]) >= 2 and T2(q) > 50e-6), key=rerr):
        if v in used: continue
        c1 = [q for q in adj[v] if q not in used and T2(q) > 40e-6]
        if not c1: continue
        d1 = min(c1, key=rerr)
        c2 = [q for q in range(nq) if q not in used and q not in (v, d1) and T2(q) > 40e-6
              and q not in adj[v] and any(q in adj[x] for x in adj[v])]
        if not c2: continue
        d2 = min(c2, key=rerr)
        used |= {v, d1, d2}
        pairs.append(dict(victim=v, d1=d1, d2=d2, rerr_v=round(rerr(v), 4),
                          rerr_d1=round(rerr(d1), 4), rerr_d2=round(rerr(d2), 4)))
        if len(pairs) >= n: break
    return pairs


def make(vbit):
    qc = QuantumCircuit(2, 1)
    if vbit: qc.x(0)
    qc.h(1); qc.delay(WIN, 0, unit="s"); qc.delay(WIN, 1, unit="s")
    qc.sdg(1); qc.h(1); qc.measure(1, 0)
    return qc


b = svc.backend(backend_name)
if reuse:
    pre = json.load(open(BASE + "sweep_prereg.json"))
    pairs = pre["devices"][backend_name]["pairs"][:npairs]
    origin = "reused verbatim from sweep_prereg.json"
else:
    pairs = pick_pairs(b, npairs)
    origin = "selected from calibration data only (outcome-independent)"

ncirc = len(pairs) * 2 * 2 * REPS          # dist x vbit x reps
est = ncirc * SEC_PER_CIRCUIT
print(f"{backend_name}: {len(pairs)} pairs -> {ncirc} circuits, est {est:.0f}s "
      f"(remaining {remaining}s, reserve {RESERVE}s)")
if est > remaining - RESERVE:
    print(f"ABORT: estimated {est:.0f}s exceeds usable budget {remaining - RESERVE:.0f}s. Nothing submitted.")
    raise SystemExit(3)
if not pairs:
    print("ABORT: no pairs met the calibration criteria."); raise SystemExit(4)

circs, labels = [], []
for pi, pr in enumerate(pairs):
    for dist, pp in (("d1", pr["d1"]), ("d2", pr["d2"])):
        for vbit in (0, 1):
            for r in range(REPS):
                circs.append(transpile(make(vbit), backend=b,
                                       initial_layout=[pr["victim"], pp],
                                       optimization_level=1, scheduling_method="asap"))
                labels.append(dict(pair=pi, victim=pr["victim"], probe=pp,
                                   dist=dist, vbit=vbit, rep=r))

tgt = b.target
snap = {}
for q in sorted({q for pr in pairs for q in (pr["victim"], pr["d1"], pr["d2"])}):
    try: re_ = tgt["measure"][(q,)].error
    except Exception: re_ = None
    try: t2 = tgt.qubit_properties[q].t2
    except Exception: t2 = None
    snap[str(q)] = dict(rerr=re_, t2=t2)
try: last_cal = str(b.properties().last_update_date)
except Exception: last_cal = None

job = SamplerV2(mode=b).run(circs, shots=SHOTS)
print(f"submitted -> {job.job_id()}  (cal {last_cal})")

json.dump(dict(backend=backend_name, tag=tag, job_id=job.job_id(), pairs=pairs,
               pair_origin=origin, labels=labels, ncirc=ncirc, est_seconds=est,
               last_calibration=last_cal, calibration_snapshot=snap,
               processor=str(getattr(b, "processor_type", None)),
               submitted_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()),
          open(BASE + f"jobs_{tag}.json", "w"), indent=1)
if not reuse:
    json.dump(dict(backend=backend_name, WIN_s=WIN, shots=SHOTS, reps=REPS, pairs=pairs,
                   selection="calibration-only, outcome-independent"),
              open(BASE + f"prereg_{tag}.json", "w"), indent=1)
print(f"wrote jobs_{tag}.json")
