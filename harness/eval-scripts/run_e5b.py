import glob,subprocess,os,pathlib,re,json
HERE = pathlib.Path(__file__).resolve().parent
ROOT=os.environ.get("ARTIFACT_ROOT", str(HERE.parents[1]))  # Artifact/ (holds lakefile.toml)
ENTRY="harness/CertifyQASMSafe.lean"; OPT=os.environ.get("AXIS2_OUT", str(HERE.parent/"axis2-out"))
LAKE=os.path.expanduser("~/.elan/bin/lake"); LEAN=os.path.expanduser("~/.elan/bin/lean")
env=dict(os.environ,PATH=os.path.expanduser("~/.elan/bin")+":"+os.environ.get("PATH",""))
files=[]
for opt in (0,1,2,3):
    for regime in ("full","confined"):
        files+=[os.path.relpath(f,ROOT) for f in sorted(glob.glob(f"{OPT}/o{opt}/{regime}/*.qasm"))]
r=subprocess.run([LAKE,"env",LEAN,"--run",ENTRY]+files,cwd=ROOT,env=env,capture_output=True,text=True)
verds={}
for ln in r.stdout.splitlines():
    m=re.match(r"(ACCEPT|REJECT|REJECT-PARSE)\s+(\S+)",ln)
    if m: verds[m.group(2)]=(m.group(1),"confined=false" in ln,"legal=false" in ln)
print("parsed",len(verds),"verdicts; rc",r.returncode)
summary={}
for opt in (0,1,2,3):
    row={}
    for regime in ("full","confined"):
        fs=[os.path.relpath(f,ROOT) for f in sorted(glob.glob(f"{OPT}/o{opt}/{regime}/*.qasm"))]
        vs=[verds[f] for f in fs if f in verds]; n=len(vs)
        if not n: continue
        row[regime]=dict(n=n,accept=sum(1 for v in vs if v[0]=="ACCEPT"),reject=sum(1 for v in vs if v[0]=="REJECT"),
            reject_parse=sum(1 for v in vs if v[0]=="REJECT-PARSE"),violations=sum(1 for v in vs if v[1]))
    summary[f"opt{opt}"]=row
json.dump(summary,open("e5_results.json","w"),indent=1); print(json.dumps(summary,indent=1))
