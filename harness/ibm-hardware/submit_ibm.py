import json, math, pathlib, sys
from qiskit import QuantumCircuit, transpile
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2

BASE = pathlib.Path(__file__).resolve().parent
for _p in pathlib.Path(__file__).resolve().parents:
    if (_p / "apikey.json").exists():
        break
else:
    raise FileNotFoundError("apikey.json not found in any parent directory of this script")
KEY = json.load(open(_p / "apikey.json"))["apikey"]
svc = QiskitRuntimeService(channel="ibm_quantum_platform", token=KEY)
backend = svc.backend("ibm_marrakesh")
tgt, nq = backend.target, backend.num_qubits
print(f"backend={backend.name} nq={nq}")

# Build adjacency from the coupling map.
adj = {i:set() for i in range(nq)}
for a,b in backend.coupling_map.get_edges(): adj[a].add(b); adj[b].add(a)
def bfs(s):
    d={s:0}; f=[s]
    while f:
        n=[]
        for u in f:
            for w in adj[u]:
                if w not in d: d[w]=d[u]+1; n.append(w)
        f=n
    return d
def rerr(q):
    try: return tgt["measure"][(q,)].error
    except (KeyError, AttributeError) as e:
        print(f"WARN q{q}: no measured readout error ({type(e).__name__}), using fallback 1.0", file=sys.stderr)
        return 1.0
def T2(q):
    try: return tgt.qubit_properties[q].t2 or 100e-6
    except (KeyError, IndexError, TypeError, AttributeError) as e:
        print(f"WARN q{q}: no measured T2 ({type(e).__name__}), using fallback 100e-6", file=sys.stderr)
        return 100e-6

# Victim selection: good readout, degree >= 2, decent T2.
victim = min((q for q in range(nq) if len(adj[q])>=2 and T2(q)>60e-6), key=rerr)
dist = bfs(victim)
probes={}
for d in (1,2,3):
    c=[q for q,dd in dist.items() if dd==d and T2(q)>40e-6]
    if c: probes[d]=min(c,key=rerr)
probes["far"]=min([q for q,dd in dist.items() if dd>=6],key=rerr)
print(f"victim=q{victim} T2={T2(victim)*1e6:.0f}us rerr={rerr(victim):.4f}")
for d,p in probes.items(): print(f"  probe d={str(d):<3} q{p:<4} T2={T2(p)*1e6:6.0f}us rerr={rerr(p):.4f} dist={dist[p]}")

# Victim drive window: M X-gates, about 40us. The probe delay matches this window.
try: dur_x = tgt["x"][(victim,)].duration or 60e-9
except (KeyError, AttributeError) as e:
    print(f"WARN q{victim}: no measured x-gate duration ({type(e).__name__}), using fallback 60e-9", file=sys.stderr)
    dur_x = 60e-9
TAU=40e-6; M=max(1,round(TAU/dur_x)); WIN=M*dur_x
print(f"dur_x={dur_x*1e9:.1f}ns M={M} window={WIN*1e6:.1f}us")

def make(pp, driven):
    qc=QuantumCircuit(2,1)   # q0 is the victim. q1 is the probe.
    qc.h(1); qc.barrier()
    if driven:
        for _ in range(M): qc.x(0)
    else:
        qc.delay(WIN,0,unit="s")
    qc.delay(WIN,1,unit="s")           # The probe idles through the victim window.
    qc.barrier(); qc.sdg(1); qc.h(1)   # Y-basis close. DeltaP = |sin(phi)|.
    qc.measure(1,0)
    return transpile(qc, backend=backend, initial_layout=[victim,pp],
                     optimization_level=1, scheduling_method="asap")

REPS=2; SHOTS=8192
circs=[]; labels=[]
for r in range(REPS):
    for d,pp in probes.items():
        for driven in (False,True):
            circs.append(make(pp,driven))
            labels.append(dict(rep=r,d=str(d),probe=pp,driven=driven))
print(f"submitting {len(circs)} circuits x {SHOTS} shots")
job=SamplerV2(mode=backend).run(circs, shots=SHOTS)
jid=job.job_id()
meta=dict(backend=backend.name, job_id=jid, victim=victim,
          probes={str(k):v for k,v in probes.items()}, dist={str(probes[k]):dist[probes[k]] for k in probes},
          T2={str(q):T2(q) for q in [victim]+list(probes.values())},
          rerr={str(q):rerr(q) for q in [victim]+list(probes.values())},
          tau_s=WIN, M=M, dur_x=dur_x, shots=SHOTS, reps=REPS, labels=labels,
          coupling_local={str(q):sorted(adj[q]) for q in [victim]+list(probes.values())})
json.dump(meta, open(BASE / "ibm_job.json","w"), indent=1)
print(f"JOB_ID={jid}\nsaved ibm_job.json")
