import json, math, pathlib, sys
from qiskit import QuantumCircuit, transpile
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2

BASE = pathlib.Path(__file__).resolve().parent
for _p in pathlib.Path(__file__).resolve().parents:
    if (_p / "apikey.json").exists():
        break
else:
    raise FileNotFoundError("apikey.json not found in any parent directory of this script")
KEY=json.load(open(_p / "apikey.json"))["apikey"]
svc=QiskitRuntimeService(channel="ibm_quantum_platform",token=KEY)
WIN=40e-6; SHOTS=8192; REPS=2

def pick_pairs(backend, npairs):
    nq=backend.num_qubits; tgt=backend.target
    adj={i:set() for i in range(nq)}
    for a,b in backend.coupling_map.get_edges(): adj[a].add(b);adj[b].add(a)
    def rerr(q):
        try:return tgt["measure"][(q,)].error
        except (KeyError, AttributeError) as e:
            print(f"WARN q{q}: no measured readout error ({type(e).__name__}), using fallback 1.0", file=sys.stderr)
            return 1.0
    def T2(q):
        try:return tgt.qubit_properties[q].t2 or 0
        except (KeyError, IndexError, TypeError, AttributeError) as e:
            print(f"WARN q{q}: no measured T2 ({type(e).__name__}), using fallback 0", file=sys.stderr)
            return 0
    used=set(); pairs=[]
    for v in sorted((q for q in range(nq) if len(adj[q])>=2 and T2(q)>50e-6), key=rerr):
        if v in used: continue
        d1=[q for q in adj[v] if q not in used and T2(q)>40e-6]
        if not d1: continue
        d1=min(d1,key=rerr)
        d2c=[q for q in range(nq) if q not in used and q not in(v,d1) and T2(q)>40e-6
             and q not in adj[v] and any(q in adj[x] for x in adj[v])]  # exactly 2 hops
        if not d2c: continue
        d2=min(d2c,key=rerr)
        used|={v,d1,d2}; pairs.append(dict(victim=v,d1=d1,d2=d2,
              rerr_v=round(rerr(v),4),rerr_d1=round(rerr(d1),4),rerr_d2=round(rerr(d2),4)))
        if len(pairs)>=npairs: break
    return pairs

def gen():
    def make(pv,pp,vbit):
        qc=QuantumCircuit(2,1)
        if vbit: qc.x(0)
        qc.h(1); qc.delay(WIN,0,unit="s"); qc.delay(WIN,1,unit="s")
        qc.sdg(1); qc.h(1); qc.measure(1,0); return qc
    return make

def build_device(name,npairs):
    b=svc.backend(name); pairs=pick_pairs(b,npairs); make=gen(); circs=[];labels=[]
    for pi,pr in enumerate(pairs):
        for dist,pp in (("d1",pr["d1"]),("d2",pr["d2"])):
            for vbit in (0,1):
                for r in range(REPS):
                    qc=make(pr["victim"],pp,vbit)
                    circs.append(transpile(qc,backend=b,initial_layout=[pr["victim"],pp],
                                 optimization_level=1,scheduling_method="asap"))
                    labels.append(dict(pair=pi,victim=pr["victim"],probe=pp,dist=dist,vbit=vbit,rep=r))
    gen_name=getattr(b,'name',name)
    proc=getattr(b,'processor_type',None)
    return b,pairs,circs,labels,proc

prereg={"WIN_s":WIN,"shots":SHOTS,"reps":REPS,"devices":{}}
jobs={}
for name,n in (("ibm_marrakesh",5),("ibm_fez",3)):
    b,pairs,circs,labels,proc=build_device(name,n)
    prereg["devices"][name]=dict(pairs=pairs,ncirc=len(circs),processor=str(proc))
    job=SamplerV2(mode=b).run(circs,shots=SHOTS)
    jobs[name]=dict(job_id=job.job_id(),labels=labels,ncirc=len(circs),processor=str(proc))
    print(f"{name}: {len(pairs)} pairs, {len(circs)} circuits, proc={proc}, JOB={job.job_id()}")
json.dump(prereg, open(BASE / "sweep_prereg.json","w"), indent=1)
json.dump(jobs, open(BASE / "sweep_jobs.json","w"), indent=1)
print("submitted; saved sweep_prereg.json + sweep_jobs.json")
