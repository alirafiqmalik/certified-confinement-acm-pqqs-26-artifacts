import glob,os,pathlib,random,subprocess,re,json
random.seed(7)
HERE = pathlib.Path(__file__).resolve().parent
# This script needs the output of run_optlevel.py (o3/confined/*.qasm). Run run_optlevel.py first.
OPT = os.environ.get("AXIS2_OUT", str(HERE.parent / "axis2-out"))
BASE=sorted(glob.glob(f"{OPT}/o3/confined/*.qasm"))
MUT=os.environ.get("FUZZ_OUT", str(HERE / "fuzz-out")); os.makedirs(MUT,exist_ok=True)
for f in glob.glob(f"{MUT}/*.qasm"): os.remove(f)
F=set(range(6,12))  # forbidden region on the 12-ring harness
GATE1={"x","sx","id","rz"}; # Also matches tokens with the rz(...) prefix.
def gate_line(ln):
    t=ln.strip()
    if not t: return None
    g=t.split()[0]
    if g in ("OPENQASM","include","qreg","creg","barrier","gate") or g.startswith("qreg") or g.startswith("qubit"): return ("hdr",)
    if g=="x" or g=="sx" or g=="id" or g.startswith("rz"): 
        qs=re.findall(r"\[(\d+)\]",t); return ("g1",g,[int(x) for x in qs][:1])
    if g in ("cz","cx"):
        qs=re.findall(r"\[(\d+)\]",t); return ("g2",g,[int(x) for x in qs][:2])
    return ("unknown",)  # A conditioned or unknown token. parseQASMSafe rejects it.
def support_and_class(lines):
    """Ground truth is a (should_reject, reason) pair. An unknown token means reject, for reason unmodellable."""
    sup=set()
    for ln in lines:
        p=gate_line(ln)
        if p is None or p[0]=="hdr": continue
        if p[0]=="unknown": return True,"unknown_token"
        sup|=set(p[2])
    return (bool(sup & F),"support_in_F" if (sup&F) else "confined")
MUTS=[]
for bf in BASE:
    lines=open(bf).read().splitlines()
    for k in range(40):
        m=list(lines); typ=random.choice(["reloc","boundary","cond","alias"])
        gidx=[i for i,l in enumerate(m) if gate_line(l) and gate_line(l)[0] in ("g1","g2")]
        if typ=="reloc" and gidx:
            i=random.choice(gidx); m[i]=re.sub(r"\[\d+\]",f"[{random.randint(6,11)}]",m[i],count=1)
        elif typ=="boundary":
            m.append("cz q[5],q[6];")
        elif typ=="cond":
            m.append(f"if(c==1) cz q[3],q[{random.randint(6,11)}];")
        elif typ=="alias" and gidx:
            i=random.choice(gidx); m[i]=re.sub(r"\[\d+\]",f"[{random.randint(6,11)}]",m[i])
        txt="\n".join(m)
        gt,reason=support_and_class(m)
        name=f"{os.path.basename(bf)[:-5]}_{typ}_{k}.qasm"
        open(f"{MUT}/{name}","w").write(txt); MUTS.append(dict(name=name,should_reject=gt,reason=reason))
json.dump(MUTS,open(f"{MUT}/ground_truth.json","w"),indent=1)
print(f"generated {len(MUTS)} mutants ({sum(m['should_reject'] for m in MUTS)} should-reject by ground truth)")
