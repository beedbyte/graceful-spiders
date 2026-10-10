"""Portable fresh Lean build; every output path is guarded outside this package."""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys
sys.dont_write_bytecode = True
from path_guard import validated_destinations

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser()
ap.add_argument("--lean", required=True, type=Path, help="Lean 4.34.0 executable")
ap.add_argument("--output", required=True, type=Path, help="new output directory outside this package")
a=ap.parse_args()
# Resolve and reserve output, derived logs and results before any package or output writes.
out, logs, result_path = validated_destinations(root, a.output)
lean=a.lean.resolve()
expected="a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2"
if sha(lean)!=expected: raise SystemExit("Lean executable SHA256 mismatch")
rows=json.loads((root/"PAYLOAD-SHA256.json").read_text(encoding="utf-8"))
for row in rows:
    p=root/row["path"]
    if not p.is_file() or p.stat().st_size!=row["bytes"] or sha(p)!=row["sha256"]:
        raise SystemExit("package payload mismatch: "+row["path"])
order=json.loads((root/"module-order.json").read_text(encoding="utf-8"))
source=root/"source"; checks=root/"checks"
if len(order)!=84 or set(order)!={p.stem for p in source.glob("*.lean")}: raise SystemExit("module order mismatch")
# Recheck immediately before creating any output destination.
out, logs, result_path = validated_destinations(root, out)
out.mkdir(parents=True); logs.mkdir()
env=os.environ.copy(); env["LEAN_PATH"]=str(out); env["PYTHONDONTWRITEBYTECODE"]="1"
results=[]
def run(path, module, expect_fail=False, emit=True):
    cmd=[str(lean),"-DwarningAsError=true"]
    if emit: cmd += ["-o",str(out/(module+".olean"))]
    p=subprocess.run(cmd+[str(path.resolve())],cwd=path.parent,env=env,text=True,encoding="utf-8",capture_output=True)
    output=p.stdout+p.stderr; (logs/(module+".log")).write_text(output,encoding="utf-8")
    results.append({"module":module,"exit":p.returncode,"log_sha256":sha(logs/(module+".log"))})
    if expect_fail:
        if p.returncode==0 or "error:" not in output or "is false" not in output: raise SystemExit("negative semantic control did not fail as expected: "+module)
    elif p.returncode!=0: raise SystemExit("Lean build failed: "+module+"\n"+output)
    return output
for name in order: run(source/(name+".lean"),name)
audit=run(checks/"Audit.lean","Audit")
closures={}
for name,body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit):
    ax=[x.strip() for x in body.split(",") if x.strip()]
    if not set(ax)<={"propext","Classical.choice","Quot.sound"}: raise SystemExit("nonstandard axiom closure: "+name)
    closures[name]=ax
if len(closures)!=9: raise SystemExit("expected nine principal axiom closures")
for p in sorted(checks.glob("Mutant*.lean")): run(p,p.stem,True,False)
result={"status":"PASS","lean_sha256":expected,"source_modules":len(order),"principal_axiom_closures":closures,"compile_rows":results}
result_path.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8")
print("FRESH_COPIED_SOURCE_BUILD_PASS")
