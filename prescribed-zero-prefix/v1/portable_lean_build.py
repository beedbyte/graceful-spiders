"""New portable build adapter. Frozen source/build scripts remain unchanged."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys
H=Path(__file__).resolve().parent
EXPECTED='a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2'
def need(x,m):
 if not x:raise RuntimeError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--lean',required=True,type=Path);p.add_argument('--build',default='portable-build');p.add_argument('--theorem',choices=['D7','D8'],default='D8');a=p.parse_args()
F=H/'research-audits'/('graceful-q10-gap-fill-formal-2026-10-09-a' if a.theorem=='D8' else 'graceful-ten-elevenths-formal-2026-10-09-a')
need(sha(a.lean)==EXPECTED,'exact recorded Windows Lean4.34.0 compiler required; different builds need separate verification')
source=json.loads((F/'source-hashes.json').read_text(encoding='utf-8'))
subprocess.run([sys.executable,'-B',str(H/'verify_package.py')],check=True)
B=(H/a.build).resolve();need(B.parent==H.resolve(),'build directory must be directly within package');need(not B.exists(),'fresh build directory required');B.mkdir()
env=os.environ.copy();env['LEAN_PATH']=str(B)
rows=[];modules=json.loads((F/'module-order.json').read_text(encoding='utf-8'))
before={m:sha(F/(m+'.lean')) for m in modules}
for m in modules:
 command=[str(a.lean.resolve()),'-DwarningAsError=true','-R',str(F.resolve()),'-o',str(B/(m+'.olean')),str((F/(m+'.lean')).resolve())]
 run=subprocess.run(command,env=env,cwd=F,capture_output=True)
 (B/(m+'.log')).write_bytes(run.stdout+run.stderr)
 rows.append({'module':m,'source_sha256':before[m],'exit_code':run.returncode})
 (B/'build-results.json').write_text(json.dumps(rows,indent=2)+'\n',encoding='utf-8')
 need(run.returncode==0,'Lean compile failed '+m);need(sha(F/(m+'.lean'))==before[m],'source changed')
 print('PASS',m,flush=True)
names=json.loads((F/'theorem-inventory.json').read_text(encoding='utf-8'));audit=(B/('GapAudit.log' if a.theorem=='D8' else 'Q11Audit.log')).read_text(encoding='utf-8');deps={}
for name in names:
 match=re.search(re.escape("'"+name+"' depends on axioms:")+r'\s*\[([^\]]*)\]',audit)
 if match:deps[name]=[v.strip() for v in match.group(1).split(',') if v.strip()]
 else:need("'"+name+"' does not depend on any axioms" in audit,'missing axiom report');deps[name]=[]
need(set(v for values in deps.values() for v in values)<={'propext','Classical.choice','Quot.sound'},'unexpected axiom')
saved=json.loads((F/'axiom-inventory.json').read_text(encoding='utf-8'))
need(deps==saved,'axiom inventory differs from frozen author inventory')
(B/'recomputed-axioms.json').write_text(json.dumps(deps,indent=2)+'\n',encoding='utf-8')
print('PASS fresh',a.theorem,'build;',len(modules),'modules and',len(names),'matching theorem axiom reports.')
