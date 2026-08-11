import json, math, pathlib
from qiskit_ibm_runtime import QiskitRuntimeService

BASE = pathlib.Path(__file__).resolve().parent
for _p in pathlib.Path(__file__).resolve().parents:
    if (_p / "apikey.json").exists():
        break
else:
    raise FileNotFoundError("apikey.json not found in any parent directory of this script")
KEY=json.load(open(_p / "apikey.json"))["apikey"]
jobs=json.load(open(BASE / "sweep_jobs.json")); prereg=json.load(open(BASE / "sweep_prereg.json"))
svc=QiskitRuntimeService(channel="ibm_quantum_platform",token=KEY)
# Check the status of every job.
for name,info in jobs.items():
    st=str(svc.job(info["job_id"]).status()); print(f"{name} {info['job_id']} status={st}")
    info["_st"]=st
if not all("DONE" in j["_st"] for j in jobs.values()):
    print("NOT_ALL_DONE"); raise SystemExit
def p1(pub):
    d=pub.data; reg=list(d.__dict__.keys())[0]; c=getattr(d,reg).get_counts(); t=sum(c.values()); return c.get('1',0)/t
def tp(a,b,n):
    se=math.sqrt(a*(1-a)/n+b*(1-b)/n); d=abs(b-a); return d,(d/se if se>0 else 0)
SHOTS=prereg["shots"]; N=SHOTS*prereg["reps"]
allpairs=[]; agree=0
for name,info in jobs.items():
    res=svc.job(info["job_id"]).result(); labels=info["labels"]
    cells={}
    for lab,pub in zip(labels,res):
        cells.setdefault(lab["pair"],{}).setdefault(lab["dist"],{}).setdefault(lab["vbit"],[]).append(p1(pub))
    for pi in sorted(cells):
        row={"device":name,"pair":pi}
        for dist in ("d1","d2"):
            v0=sum(cells[pi][dist][0])/len(cells[pi][dist][0]); v1=sum(cells[pi][dist][1])/len(cells[pi][dist][1])
            dp,z=tp(v0,v1,N); row[dist]={"dP":round(dp,4),"z":round(z,1)}
        leak_d1=row["d1"]["z"]>=5; leak_d2=row["d2"]["z"]>=5
        row["prediction_holds"]=bool(leak_d1 and not leak_d2)  # leak@d1, null@d2
        row["note"]=("OK" if row["prediction_holds"] else
                     ("d1 no-leak (certifier still REJECTs=safe-conservative)" if not leak_d1 else
                      "LEAK@d2 breaks NN → motivates k>1"))
        if row["prediction_holds"]: agree+=1
        allpairs.append(row)
print(f"\n=== SWEEP: {len(allpairs)} pairs, prediction (leak@d1 & null@d2) holds on {agree}/{len(allpairs)} ===")
for r in allpairs:
    print(f"  {r['device'][:13]:<13} pair{r['pair']} d1(dP={r['d1']['dP']},z={r['d1']['z']}) "
          f"d2(dP={r['d2']['dP']},z={r['d2']['z']})  {'HOLDS' if r['prediction_holds'] else 'X'}  {r['note']}")
json.dump({"agree":agree,"total":len(allpairs),"pairs":allpairs},open(BASE / "sweep_results.json","w"),indent=1)
