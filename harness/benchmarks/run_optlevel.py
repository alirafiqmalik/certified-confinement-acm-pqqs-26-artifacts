import os,glob,json,pathlib,time
from qiskit.qasm2 import load, dumps, LEGACY_CUSTOM_INSTRUCTIONS
from qiskit import transpile
from qiskit.transpiler import CouplingMap
from qiskit.converters import circuit_to_dag, dag_to_circuit
HERE = pathlib.Path(__file__).resolve().parent
# QASMBench (PNNL) is an external benchmark suite. This artifact does not ship it.
SMALL=os.environ.get("QASMBENCH_SMALL", str(HERE.parent/"QASMBench"/"small"))
OUT=os.environ.get("AXIS2_OUT", str(HERE.parent/"axis2-out"))
BASIS=["x","sx","rz","cz","id"]; RING12=CouplingMap([[i,(i+1)%12] for i in range(12)])
PATH6=CouplingMap([[i,i+1] for i in range(5)])
def strip(qc):
    qc=qc.remove_final_measurements(inplace=False) or qc; dag=circuit_to_dag(qc)
    for n in list(dag.op_nodes()):
        if n.op.name in ("measure","reset","barrier"): dag.remove_op_node(n)
    return dag_to_circuit(dag)
rows=[]
for opt in (0,1,2,3):
    os.makedirs(f"{OUT}/o{opt}/full",exist_ok=True); os.makedirs(f"{OUT}/o{opt}/confined",exist_ok=True)
for d in sorted(glob.glob(f"{SMALL}/*_n*")):
    name=os.path.basename(d); src=os.path.join(d,name+".qasm")
    if not os.path.exists(src): continue
    try:
        qc=strip(load(src,include_path=(d,SMALL),custom_instructions=LEGACY_CUSTOM_INSTRUCTIONS))
    except Exception as e: continue
    nq=qc.num_qubits
    if nq>12: continue
    for opt in (0,1,2,3):
        try:
            t0=time.perf_counter(); tB=transpile(qc,coupling_map=RING12,basis_gates=BASIS,optimization_level=opt,seed_transpiler=7); tt=time.perf_counter()-t0
            open(f"{OUT}/o{opt}/full/{name}.qasm","w").write(dumps(tB))
            rec=dict(name=name,nq=nq,opt=opt,transpile_s=round(tt,4),ngates=len(tB.data))
            if nq<=6:
                tA=transpile(qc,coupling_map=PATH6,basis_gates=BASIS,optimization_level=opt,seed_transpiler=7)
                open(f"{OUT}/o{opt}/confined/{name}.qasm","w").write(dumps(tA))
                rec["confined"]=True
            rows.append(rec)
        except Exception as e: rows.append(dict(name=name,opt=opt,error=str(e)[:80]))
json.dump(rows,open(f"{OUT}/manifest.json","w"),indent=1)
ok=[r for r in rows if "error" not in r]
print(f"opt-level transpile done: {len(ok)} circuit-transpiles across opt 0-3")
for opt in (0,1,2,3):
    fs=len(glob.glob(f"{OUT}/o{opt}/full/*.qasm")); cs=len(glob.glob(f"{OUT}/o{opt}/confined/*.qasm"))
    tt=sum(r["transpile_s"] for r in ok if r["opt"]==opt)
    print(f"  opt{opt}: full={fs} confined={cs} total_transpile={tt:.2f}s")
