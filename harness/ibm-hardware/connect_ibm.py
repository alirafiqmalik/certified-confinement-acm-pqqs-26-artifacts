import json, pathlib, sys
from qiskit_ibm_runtime import QiskitRuntimeService

for _p in pathlib.Path(__file__).resolve().parents:
    if (_p / "apikey.json").exists():
        break
else:
    raise FileNotFoundError("apikey.json not found in any parent directory of this script")
KEY = json.load(open(_p / "apikey.json"))["apikey"]

svc = None
for ch in ("ibm_quantum_platform", "ibm_cloud", "ibm_quantum"):
    try:
        svc = QiskitRuntimeService(channel=ch, token=KEY)
        print(f"CONNECTED via channel={ch}")
        break
    except Exception as e:
        print(f"  channel {ch} failed: {type(e).__name__}: {str(e)[:120]}")
if svc is None:
    sys.exit("could not connect on any channel")

print("\n=== backends ===")
for b in svc.backends():
    try:
        st = b.status()
        cfg = b.configuration()
        print(f"  {b.name:<22} qubits={cfg.n_qubits:<4} sim={cfg.simulator} "
              f"operational={st.operational} pending_jobs={st.pending_jobs}")
    except Exception as e:
        print(f"  {b.name}: status err {type(e).__name__}: {str(e)[:80]}")
try:
    lb = svc.least_busy(operational=True, simulator=False)
    print(f"\nleast_busy real device: {lb.name} (pending={lb.status().pending_jobs})")
except Exception as e:
    print(f"least_busy err: {type(e).__name__}: {str(e)[:120]}")
