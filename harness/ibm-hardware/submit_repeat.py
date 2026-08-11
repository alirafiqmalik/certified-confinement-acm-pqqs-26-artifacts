"""
Second-snapshot REPLICATION of the n=8 leak sweep (paper question E4).

Purpose: this script removes the paper's "single calibration snapshot" hedge.

Design rules (these are the scientific content of this script, not boilerplate):
 1. The script reads the 8 victim/probe pairs VERBATIM from `sweep_prereg.json`. It
    deliberately does NOT re-run `pick_pairs()`. A re-selection from the *new*
    calibration silently picks whichever qubits look best today. That is exactly the
    cherry-picking that the pre-registration exists to rule out. Replication means
    the SAME pairs on a DIFFERENT snapshot.
 2. The circuit construction is byte-identical in structure to `submit_sweep.py`:
    Y-basis Ramsey, tau=40us, 8192 shots, 2 reps, asap scheduling.
 3. The script records the live calibration snapshot at submission time: readout
    error, T2, and last_update_date from the backend. The first sweep did not record
    this snapshot. So the first sweep's chronology rested on argument alone, with no
    direct proof. This run fixes that gap for itself.

The script reads the token at runtime, from apikey.json. It never prints the token.
It never writes the token to any artifact.
"""
import json, os, pathlib, datetime

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

svc = QiskitRuntimeService(channel="ibm_quantum_platform", token=KEY, **_INST)

pre = json.load(open(BASE + "sweep_prereg.json"))
WIN = pre["WIN_s"]; SHOTS = pre["shots"]; REPS = pre["reps"]


def make(vbit):
    """Identical to submit_sweep.py. The victim holds the secret in its STATE. The probe
    runs a Y-basis Ramsey. So the readout is linear in the accumulated phase. A plain
    H..H Ramsey measures sin^2(theta/2). This value is even in theta, and blind to a
    sign flip."""
    qc = QuantumCircuit(2, 1)
    if vbit:
        qc.x(0)
    qc.h(1)
    qc.delay(WIN, 0, unit="s")
    qc.delay(WIN, 1, unit="s")
    qc.sdg(1)
    qc.h(1)
    qc.measure(1, 0)
    return qc


def snapshot(b, qubits):
    tgt = b.target
    snap = {}
    for q in sorted(set(qubits)):
        try: re_ = tgt["measure"][(q,)].error
        except Exception: re_ = None
        try: t2 = tgt.qubit_properties[q].t2
        except Exception: t2 = None
        snap[str(q)] = dict(rerr=re_, t2=t2)
    return snap


out = {"submitted_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
       "note": "second calibration snapshot; pairs reused verbatim from sweep_prereg.json",
       "devices": {}}

for name in ("ibm_marrakesh", "ibm_fez"):
    b = svc.backend(name)
    pairs = pre["devices"][name]["pairs"]
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
    qubits = [q for pr in pairs for q in (pr["victim"], pr["d1"], pr["d2"])]
    try: last_cal = str(b.properties().last_update_date)
    except Exception: last_cal = None

    job = SamplerV2(mode=b).run(circs, shots=SHOTS)
    print(f"{name}: submitted {len(circs)} circuits -> {job.job_id()}  (cal {last_cal})")

    out["devices"][name] = dict(job_id=job.job_id(), labels=labels, pairs=pairs,
                                ncirc=len(circs), processor=str(getattr(b, "processor_type", None)),
                                last_calibration=last_cal, calibration_snapshot=snapshot(b, qubits))

json.dump(out, open(BASE + "repeat_jobs.json", "w"), indent=1)
print("wrote repeat_jobs.json")
