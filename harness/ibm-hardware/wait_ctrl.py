import json, time, math, pathlib, sys
from qiskit_ibm_runtime import QiskitRuntimeService

BASE = pathlib.Path(__file__).resolve().parent
for _p in pathlib.Path(__file__).resolve().parents:
    if (_p / "apikey.json").exists():
        break
else:
    raise FileNotFoundError("apikey.json not found in any parent directory of this script")
KEY=json.load(open(_p / "apikey.json"))["apikey"]
m=json.load(open(BASE / "ibm_ctrl_job.json")); svc=QiskitRuntimeService(channel="ibm_quantum_platform",token=KEY)
job=svc.job(m["job_id"]); t0=time.time()
while True:
    st=str(job.status()); el=int(time.time()-t0); print(f"[{el}s] {st}",flush=True)
    if any(k in st for k in("DONE","ERROR","CANCELLED")): break
    if el>520: print("STILL_WAITING"); sys.exit(0)
    time.sleep(20)
if "DONE" not in st: print("ended",st); sys.exit(1)
res=job.result(); SHOTS=m["shots"]; N=SHOTS*m["reps"]
def p1(pub):
    d=pub.data; reg=list(d.__dict__.keys())[0]; c=getattr(d,reg).get_counts(); t=sum(c.values()); return c.get('1',0)/t
cells={}
for lab,pub in zip(m["labels"],res): cells.setdefault(lab["d"],{}).setdefault(lab["cond"],[]).append(p1(pub))
def tp(pa,pb,n): se=math.sqrt(pa*(1-pa)/n+pb*(1-pb)/n); d=abs(pb-pa); return d,(d/se if se>0 else 0)
print("\n=== CONTROL: static-ZZ vs pure-drive crosstalk (ibm_marrakesh q%d) ==="%m["victim"])
out=[]
for d in ("1","2","3","far"):
    if d not in cells: continue
    i=sum(cells[d]["idle0"])/len(cells[d]["idle0"]); s=sum(cells[d]["static1"])/len(cells[d]["static1"]); dr=sum(cells[d]["driven0"])/len(cells[d]["driven0"])
    dps,zs=tp(i,s,N); dpd,zd=tp(i,dr,N)
    out.append(dict(d=d,probe=m["probes"][d],P1_idle=round(i,4),P1_static1=round(s,4),P1_driven0=round(dr,4),
                    static_dP=round(dps,4),static_z=round(zs,2),drive_dP=round(dpd,4),drive_z=round(zd,2)))
    print(f"  d={d:<3} q{m['probes'][d]:<4} idle={i:.4f} static|1>={s:.4f} driven->|0>={dr:.4f} | "
          f"staticZZ dP={dps:.4f}(z={zs:.1f})  pureDrive dP={dpd:.4f}(z={zd:.1f})")
json.dump(dict(meta=m,results=out),open(BASE / "ibm_ctrl_results.json","w"),indent=1); print("\nwrote ibm_ctrl_results.json DONE")
