"""Verify or compile the fixed-k71 Lean source package."""
import argparse,hashlib,json,os,re,shutil,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok,msg):
 if not ok: raise RuntimeError(msg)
def verify():
 idx=HERE/"SHA256SUMS.txt"; need(idx.is_file(),"checksum index missing"); listed={}
 for line in idx.read_text(encoding="ascii").splitlines():
  h,rel=line.split("  ",1); need(rel not in listed and ".." not in Path(rel).parts,"invalid index path"); listed[rel]=h
 actual={p.relative_to(HERE).as_posix() for p in HERE.rglob("*") if p.is_file()}; need(actual==set(listed)|{"SHA256SUMS.txt"},"package inventory mismatch")
 for rel,h in listed.items(): need(sha(HERE/rel)==h,"package hash mismatch: "+rel)
 order=json.loads((HERE/"build-order.json").read_text()); hashes=json.loads((HERE/"source-sha256.json").read_text()); need(len(order)==45 and len(set(order))==45 and set(order)==set(hashes),"module order")
 need({p.stem for p in (HERE/"source").glob("*.lean")}==set(order),"source set"); seen=set()
 for mod in order:
  p=HERE/"source"/(mod+".lean"); data=p.read_bytes(); need(sha(p)==hashes[mod],"source map: "+mod)
  for imp in re.findall(r"^import\s+([A-Za-z0-9_.]+)",data.decode(),re.M):
   if imp in hashes: need(imp in seen,"forward local import: "+mod)
   else: need(imp.split(".")[0] in {"Init","Std","Lean"},"unpackaged import: "+imp)
  seen.add(mod)
 return order,len(listed)
def main():
 ap=argparse.ArgumentParser(description=__doc__); ap.add_argument("--check",action="store_true"); ap.add_argument("--lean",default="lean"); ap.add_argument("--output",type=Path); a=ap.parse_args(); order,n=verify()
 if a.check: print(json.dumps({"status":"PASS","sources":len(order),"indexed_files":n})); return
 need(a.output is not None,"--output required"); out=a.output.resolve(); need(not out.exists(),"output exists"); need(not out.is_relative_to(HERE),"output must be outside package")
 lean=shutil.which(a.lean) or str(Path(a.lean).resolve()); version=subprocess.run([lean,"--version"],capture_output=True,text=True,encoding="utf-8",check=True).stdout; need("4.34.0" in version,"Lean 4.34.0 required"); out.mkdir(parents=True); env=os.environ.copy(); env["LEAN_PATH"]=str(out); env.pop("LEAN_SRC_PATH",None); rows=[]
 for mod in order:
  p=subprocess.run([lean,"-DwarningAsError=true","-o",str(out/(mod+".olean")),mod+".lean"],cwd=HERE/"source",env=env,capture_output=True,text=True,encoding="utf-8"); (out/(mod+".log")).write_text(p.stdout+p.stderr,encoding="utf-8"); rows.append({"module":mod,"source_sha256":sha(HERE/"source"/(mod+".lean")),"exit_code":p.returncode}); (out/"build-record.json").write_text(json.dumps({"lean_version":version.strip(),"modules":rows},indent=2)+"\n",encoding="utf-8")
  if p.returncode: raise RuntimeError("Lean failed: "+mod+"\n"+p.stdout+p.stderr)
 verify(); print(json.dumps({"status":"PASS","compiled_modules":len(rows),"indexed_files":n}))
if __name__=="__main__": main()
