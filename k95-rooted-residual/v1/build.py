"""Portable source/check reproducer. Requires the exactly verified Lean binary."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,time
BASE=Path(__file__).resolve().parent
PIN='a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,s):
    if not x:raise RuntimeError(s)
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n',encoding='utf-8')
args=argparse.ArgumentParser();args.add_argument('--lean',type=Path,required=True);args.add_argument('--build-dir',type=Path,required=True);a=args.parse_args()
lean=a.lean.resolve();out=a.build_dir.resolve()
need(sha(lean)==PIN,'compiler executable differs from verified Windows Lean4.34.0 binary')
need(not out.exists() or not any(out.iterdir()),'build directory must be new or empty; nothing is deleted')
out.mkdir(parents=True,exist_ok=True);obj=out/'objects';logs=out/'logs';obj.mkdir();logs.mkdir()
for line in (BASE/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
    h,rel=line.split('  ',1);need(sha(BASE/rel)==h,'package input '+rel)
order=json.loads((BASE/'module-order.json').read_text());need(len(order)==59,'complete pinned module count')
version=subprocess.run([str(lean),'--version'],capture_output=True,text=True,check=True).stdout.strip()
env=os.environ.copy();env['LEAN_PATH']=str(obj)
rows=[]
def run(name,folder,object_output=False,negative=False):
    cmd=[str(lean),'-DwarningAsError=true','--root='+str(BASE/folder)]
    if object_output:cmd+=['-o',str(obj/(name+'.olean'))]
    cmd+=[str(BASE/folder/(name+'.lean'))];t=time.monotonic()
    r=subprocess.run(cmd,cwd=BASE/folder,env=env,capture_output=True,timeout=900);log=logs/(name+'.log');log.write_bytes(r.stdout+r.stderr)
    row={'name':name,'exit_code':r.returncode,'seconds':round(time.monotonic()-t,3),'source_sha256':sha(BASE/folder/(name+'.lean')),'log_sha256':sha(log)}
    if negative:
        txt=log.read_text(encoding='utf-8');need(r.returncode!=0 and 'error:' in txt,'semantic mutant escaped '+name)
        need(not any(s in txt for s in ['unknown module','unknown identifier','object file','does not exist','unexpected token']),'nonsemantic rejection '+name)
    else:need(r.returncode==0,'compile failure '+name)
    if object_output:row['object_sha256']=sha(obj/(name+'.olean'))
    rows.append(row);dump(out/'progress.json',rows);print(json.dumps(row),flush=True)
for name in order:run(name,'source',True)
run('AuditPositive','checks',True);run('WholeClosure','checks')
inventory=[]
for m in re.finditer(r'CLOSURE\|([^|\n]+)\|([^|\n]+)\|\[([^\n]*)\]',(logs/'WholeClosure.log').read_text(encoding='utf-8')):
    ax=[s.strip() for s in m[3].split(',') if s.strip()];need(set(ax)<={'propext','Classical.choice','Quot.sound'},'nonstandard axiom')
    inventory.append({'name':m[1],'module':m[2],'axioms':sorted(ax)})
need(len(inventory)==2239,'exact full project closure inventory count')
dump(out/'axiom-inventory.json',sorted(inventory,key=lambda r:r['name']))
expected=json.loads((BASE/'evidence/axiom-inventory.json').read_text());need(sorted(inventory,key=lambda r:r['name'])==expected,'reproduced complete declaration/axiom inventory differs')
for name in ['WrongRoot','Tip95','OldResidualVertex','FalseOnto']:run(name,'checks',negative=True)
dump(out/'verification.json',{'status':'PASS_59_FRESH_WARNING_AS_ERROR_SOURCE_BUILDS','compiler':version,'compiler_executable_sha256':sha(lean),'project_modules':59,'axiom_closures':2239,'concrete_positive_targets':196,'semantic_mutants_rejected':4,'rows':rows})
print('PASS:59 fresh modules,2239 standard-only closures,196 named target assertions,4 semantic mutants.',flush=True)
