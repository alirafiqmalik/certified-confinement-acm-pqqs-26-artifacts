import glob,os,pathlib,time,json
from mqt import qcec
HERE = pathlib.Path(__file__).resolve().parent
SMALL=os.environ.get("QASMBENCH_SMALL", str(HERE.parent/"QASMBench"/"small"))
OPT=os.environ.get("AXIS2_OUT", str(HERE.parent/"axis2-out"))+"/o3/full"
rows=[]
for tq in sorted(glob.glob(f"{OPT}/*.qasm"))[:8]:
    name=os.path.basename(tq)[:-5]; orig=f"{SMALL}/{name}/{name}.qasm"
    if not os.path.exists(orig): continue
    try:
        t0=time.perf_counter(); res=qcec.verify(orig,tq); dt=time.perf_counter()-t0
        rows.append(dict(circuit=name,equivalence=str(res.equivalence),qcec_s=round(dt,4)))
    except Exception as e: rows.append(dict(circuit=name,error=str(e)[:70]))
ok=[r for r in rows if "error" not in r]
print(f"QCEC equivalence checks (context only, NOT a speed claim): {len(ok)} circuits")
for r in ok: print(f"  {r['circuit']:<22} equiv={r['equivalence']:<28} qcec_time={r['qcec_s']}s")
if ok:
    import statistics as st
    print(f"  median QCEC equiv-check time: {st.median([r['qcec_s'] for r in ok]):.4f}s")
json.dump(rows,open("qcec_results.json","w"),indent=1)
print("\nCapability point: QCEC decides functional EQUIVALENCE (Θ(2ⁿ)/QMA-hard) but has NO")
print("notion of tenant regions/confinement — it cannot express or check the security property.")
