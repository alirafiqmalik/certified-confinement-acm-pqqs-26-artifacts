import json, time, math, pathlib, sys
from qiskit_ibm_runtime import QiskitRuntimeService

BASE = pathlib.Path(__file__).resolve().parent
for _p in pathlib.Path(__file__).resolve().parents:
    if (_p / "apikey.json").exists():
        break
else:
    raise FileNotFoundError("apikey.json not found in any parent directory of this script")
KEY = json.load(open(_p / "apikey.json"))["apikey"]
meta = json.load(open(BASE / "ibm_job.json"))
svc = QiskitRuntimeService(channel="ibm_quantum_platform", token=KEY)
job = svc.job(meta["job_id"])

t0=time.time()
while True:
    st=str(job.status())
    el=int(time.time()-t0)
    print(f"[{el}s] status={st}", flush=True)
    if st in ("DONE","ERROR","CANCELLED") or "DONE" in st or "ERROR" in st or "CANCELLED" in st:
        break
    if el>520:
        print("STILL_WAITING (re-run to keep polling)"); sys.exit(0)
    time.sleep(20)

if "DONE" not in st:
    print(f"job ended {st}"); 
    try: print(job.error_message())
    except Exception as e: print(f"(could not retrieve error message: {type(e).__name__}: {e})")
    sys.exit(1)

res=job.result()
labels=meta["labels"]; SHOTS=meta["shots"]
# Collect P(1) for each (rep, d, driven) combination.
def p1_of(pub):
    d=pub.data
    reg=list(d.__dict__.keys())[0] if hasattr(d,'__dict__') else 'c'
    arr=getattr(d, reg)
    c=arr.get_counts()
    tot=sum(c.values()); return c.get('1',0)/tot
cells={}
for lab,pub in zip(labels,res):
    p1=p1_of(pub)
    cells.setdefault((lab["d"]),{}).setdefault(lab["driven"],[]).append(p1)
def two_prop(pa,pb,n):
    se=math.sqrt(pa*(1-pa)/n+pb*(1-pb)/n); d=abs(pb-pa); z=d/se if se>0 else 0
    return d,z,(d-1.96*se,d+1.96*se)
print("\n=== RESULTS ibm_marrakesh (victim q%d driven-crosstalk, Y-basis probe) ==="%meta["victim"])
out=[]
order=["1","2","3","far"]
for d in order:
    idle=sum(cells[d][False])/len(cells[d][False])
    drv =sum(cells[d][True]) /len(cells[d][True])
    dp,z,ci=two_prop(idle,drv,SHOTS*meta["reps"])
    v="LEAK(>=5s)" if z>=5 else ("marginal" if z>=3 else "no signal")
    out.append(dict(d=d,probe=meta["probes"][d],P1_idle=round(idle,4),P1_driven=round(drv,4),
                    deltaP=round(dp,4),z=round(z,2),ci=[round(ci[0],4),round(ci[1],4)],verdict=v))
    print(f"  d={d:<3} q{meta['probes'][d]:<4} P1(idle)={idle:.4f} P1(driven)={drv:.4f} "
          f"DeltaP={dp:.4f} z={z:6.2f} [{ci[0]:.4f},{ci[1]:.4f}] {v}")
json.dump(dict(meta=meta,results=out), open(BASE / "ibm_results.json","w"),indent=1)
print("\nwrote ibm_results.json  DONE")
