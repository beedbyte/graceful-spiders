"""Verify this source package or build every local module in a fresh object tree."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess
P=Path(__file__).resolve().parent
def need(x,m):
    if not x: raise RuntimeError(m)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def index(p):
    need(p.is_file(),'required index missing: '+p.name)
    out={}
    for line in p.read_text(encoding='utf-8').splitlines():
        h,r=line.split('  ',1)
        need(re.fullmatch('[0-9a-f]{64}',h) and r not in out,'invalid index record')
        f=(P/r).resolve();need(f.is_relative_to(P) and f.is_file(),'unsafe/missing payload '+r)
        need(sha(f)==h,'payload hash mismatch: '+r);out[r]=h
    return out
def verify():
    payload=index(P/'SHA256SUMS.txt')
    actual={x.relative_to(P).as_posix() for x in P.rglob('*') if x.is_file()}
    need(actual==set(payload)|{'SHA256SUMS.txt'},'unexpected or missing payload')
    need(not any(Path(r).suffix in ('.olean','.ilean','.o','.exe','.pyc') for r in payload),'compiled object included')
    sources=index(P/'SOURCE-SHA256SUMS.txt')
    expected={r for r in payload if r.startswith(('source/','checks/'))}
    need(set(sources)==expected,'source index inventory')
    need(len([r for r in sources if r.startswith('source/')])==79,'79 transitive sources')
    need(len([r for r in sources if r.startswith('checks/')])==9,'9 independent query sources')
    provenance=json.loads((P/'provenance.json').read_text(encoding='utf-8'))
    for r,v in provenance['origins'].items(): need(payload.get(r)==v['sha256'],'origin hash '+r)
    need(len(provenance['origins'])==88,'79+9 pinned source origins')
    modules={Path(r).stem:r for r in sources if r.startswith('source/')}
    deps={}
    for name,r in modules.items():
        imports=[d for m in re.finditer(r'^\s*import\s+([^\n]+)',(P/r).read_text(encoding='utf-8-sig'),re.M) for d in m.group(1).split('--')[0].split()]
        for d in imports: need(d in modules or d.split('.')[0] in ('Init','Lean','Std'),'missing transitive import '+d)
        deps[name]=[d for d in imports if d in modules]
    order=[];pending=set(modules)
    while pending:
        ready=sorted(n for n in pending if all(d in order for d in deps[n]));need(ready,'dependency cycle')
        order.extend(ready);pending.difference_update(ready)
    reachable=set()
    def visit(n):
        if n in reachable:return
        reachable.add(n)
        for d in deps[n]:visit(d)
    visit('EvenRootedPrefix');need(reachable==set(modules),'nonminimal or incomplete transitive tree')
    return {'status':'PACKAGE_CHECK_PASS','payloads':len(payload),'source_modules':79,'query_sources':9,'archived_evidence_hashes':4,'index_sha256':sha(P/'SHA256SUMS.txt')},order
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');ap.add_argument('--lean');ap.add_argument('--output',type=Path)
    a=ap.parse_args();result,order=verify()
    if a.check: print(json.dumps(result,sort_keys=True));return
    need(a.output is not None,'provide --output as a new directory outside the package')
    out=a.output.resolve();need(not out.exists() and not out.is_relative_to(P),'output must be absent and outside package')
    lean=Path(a.lean or shutil.which('lean') or '').resolve();need(lean.is_file(),'provide Lean 4.34.0 with --lean')
    version=subprocess.check_output([str(lean),'--version'],text=True).strip();need('Lean (version 4.34.0,' in version,'Lean 4.34.0 required')
    out.mkdir(parents=True);src=out/'source';obj=out/'objects';logs=out/'logs'
    src.mkdir();obj.mkdir();logs.mkdir()
    for folder in ('source','checks'):
        for p in (P/folder).glob('*.lean'):shutil.copyfile(p,src/p.name)
    env=os.environ.copy();env['LEAN_PATH']=str(obj);env.pop('LEAN_SRC_PATH',None)
    records=[]
    def run(name,negative=None):
        proc=subprocess.run([str(lean),'-DwarningAsError=true','-o',str(obj/(name+'.olean')),name+'.lean'],cwd=src,env=env,capture_output=True,text=True,encoding='utf-8')
        text=proc.stdout+proc.stderr;log=logs/(name+'.log');log.write_text(text,encoding='utf-8')
        if negative:
            need(proc.returncode!=0 and 'error:' in text.lower() and negative in text.lower(),'ineffective negative control '+name)
            need(not (obj/(name+'.olean')).exists(),'negative object produced '+name)
        else: need(proc.returncode==0,'compilation failed '+name+'; see '+str(log))
        records.append({'module':name,'exit':proc.returncode,'source_sha256':sha(src/(name+'.lean')),'log_sha256':sha(log),'negative_marker':negative})
        return text
    for i,n in enumerate(order,1):run(n);print(f'[{i}/79] {n}',flush=True)
    run('ReplaySupport');positive=run('Positive')
    need('CLOSURES_CHECKED 3583' in positive,'closure count changed')
    need('expanded_universal' in positive and 'all_even_prefix' in positive,'expanded theorem absent')
    negatives={'WrongRoot':'is false','DepthOne':'is false','Tip':'is false','OddLength':'is false','BelowThreshold':'is false','FalseOnto':'type mismatch','WrongNamedSide':'type mismatch'}
    for n,marker in negatives.items():run(n,marker)
    result.update(status='FRESH_BUILD_AND_CONTROLS_PASS',lean_version=version,lean_sha256=sha(lean),closures=3583,positive_named_triangle_cases=16,negative_controls=7,records=records)
    (out/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='records'},sort_keys=True))
if __name__=='__main__':main()
