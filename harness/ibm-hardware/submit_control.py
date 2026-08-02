import json, pathlib
from qiskit import QuantumCircuit, transpile
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2

BASE = pathlib.Path(__file__).resolve().parent
for _p in pathlib.Path(__file__).resolve().parents:
    if (_p / "apikey.json").exists():
        break
else:
    raise FileNotFoundError("apikey.json not found in any parent directory of this script")
KEY=json.load(open(_p / "apikey.json"))["apikey"]
m=json.load(open(BASE / "ibm_job.json"))
svc=QiskitRuntimeService(channel="ibm_quantum_platform",token=KEY)
backend=svc.backend(m["backend"]); victim=m["victim"]; probes=m["probes"]
WIN=m["tau_s"]; M=m["M"]; Me=M if M%2==0 else M-1   # An even M ends in state |0>, but the qubit is still driven.
SHOTS=8192; REPS=2
def make(pp, cond):
    qc=QuantumCircuit(2,1); qc.h(1); qc.barrier()
    if cond=="idle0":   qc.delay(WIN,0,unit="s")
    elif cond=="static1": qc.x(0); qc.delay(WIN,0,unit="s")      # Final state |1>. The qubit is NOT driven.
    elif cond=="driven0":
        for _ in range(Me): qc.x(0)                              # Driven. The qubit returns to state |0>.
    qc.delay(WIN,1,unit="s"); qc.barrier(); qc.sdg(1); qc.h(1); qc.measure(1,0)
    return transpile(qc, backend=backend, initial_layout=[victim,int(pp)],
                     optimization_level=1, scheduling_method="asap")
circs=[]; labels=[]
for r in range(REPS):
    for d,pp in probes.items():
        for cond in ("idle0","static1","driven0"):
            circs.append(make(pp,cond)); labels.append(dict(rep=r,d=d,probe=int(pp),cond=cond))
job=SamplerV2(mode=backend).run(circs,shots=SHOTS)
m2=dict(m); m2["job_id"]=job.job_id(); m2["labels"]=labels; m2["Me"]=Me; m2["kind"]="control"
json.dump(m2, open(BASE / "ibm_ctrl_job.json","w"), indent=1)
print("CTRL_JOB_ID=",job.job_id(),"circuits=",len(circs))
