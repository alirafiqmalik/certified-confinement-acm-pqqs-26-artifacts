import glob,subprocess,os,pathlib,re,json
HERE = pathlib.Path(__file__).resolve().parent
ROOT=os.environ.get("ARTIFACT_ROOT", str(HERE.parents[1]))  # Artifact/ (holds lakefile.toml)
LAKE=os.path.expanduser("~/.elan/bin/lake"); LEAN=os.path.expanduser("~/.elan/bin/lean")
env=dict(os.environ,PATH=os.path.expanduser("~/.elan/bin")+":"+os.environ.get("PATH",""))
MUT=os.environ.get("FUZZ_OUT", str(HERE/"fuzz-out"))
gt={m["name"]:m for m in json.load(open(f"{MUT}/ground_truth.json"))}
files=[os.path.relpath(f,ROOT) for f in sorted(glob.glob(f"{MUT}/*.qasm"))]
def run(entry):
    r=subprocess.run([LAKE,"env",LEAN,"--run",entry]+files,cwd=ROOT,env=env,capture_output=True,text=True)
    v={}
    for ln in r.stdout.splitlines():
        m=re.match(r"(ACCEPT|REJECT|REJECT-PARSE)\s+(\S+)",ln)
        if m: v[os.path.basename(m.group(2))]=m.group(1)
    return v
old=run("harness/CertifyQASM.lean")       # parseQASM (unsound skip)
new=run("harness/CertifyQASMSafe.lean")   # parseQASMSafe
def tally(v,label):
    n=len(v); acc=sum(1 for x in v.values() if x=="ACCEPT")
    # Every mutant has ground truth REJECT. So ACCEPT here means a false accept.
    fa=[k for k,x in v.items() if x=="ACCEPT"]
    print(f"{label}: {n} mutants, ACCEPT(false-accept)={len(fa)}, caught={n-len(fa)} ({100*(n-len(fa))/n:.1f}%)")
    return dict(n=n,false_accepts=len(fa),caught=n-len(fa),examples_fa=fa[:5])
res=dict(old=tally(old,"OLD parseQASM"),new=tally(new,"NEW parseQASMSafe"),total_mutants=len(files))
json.dump(res,open(f"{MUT}/fuzz_results.json","w"),indent=1)
print("FUZZ_DONE")
