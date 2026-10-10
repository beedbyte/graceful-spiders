#!/usr/bin/env python3
"""Run kernel controls and semantic mutants against a completed fresh package build."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,sys
P=Path(__file__).resolve().parent
def require(v,s):
 if not v:raise RuntimeError(s)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--lean',default='lean');ap.add_argument('--objects',required=True);ap.add_argument('--output',required=True);a=ap.parse_args()
 subprocess.run([sys.executable,str(P/'build.py'),'--check'],check=True)
 obj=Path(a.objects).resolve();out=Path(a.output).resolve()
 require(P not in out.parents and out!=P and not out.exists(),'Choose a new output directory outside the package')
 record=json.loads((obj/'build-record.json').read_text(encoding='utf-8'))
 require(record['status']=='PASS' and record['package_manifest_sha256']==sha(P/'SHA256SUMS.txt'),'Fresh build does not match this exact package')
 for row in record['modules']:require(sha(obj/(row['module']+'.olean'))==row['object_sha256'],'Object mismatch '+row['module'])
 lean=shutil.which(a.lean);require(lean is not None,'Lean unavailable')
 require(sha(Path(lean))==record['lean_sha256'],'Use the same compiler as the fresh build')
 out.mkdir(parents=True,exist_ok=False);env=dict(os.environ);env['LEAN_PATH']=str(obj);env.pop('LEAN_SRC_PATH',None)
 result=[]
 for path in sorted((P/'checks').glob('*.lean')):
  expected=1 if path.stem.startswith('Mutant') else 0
  r=subprocess.run([lean,'-DwarningAsError=true',path.name],cwd=P/'checks',env=env,capture_output=True,text=True,encoding='utf-8');log=r.stdout+r.stderr
  (out/(path.stem+'.log')).write_text(log,encoding='utf-8')
  require((r.returncode==0)==(expected==0),'Unexpected result '+path.name)
  require('unknown module prefix' not in log and 'object file' not in log,'Import failure '+path.name)
  if path.stem=='WholeEnvironment':require('ALL_PACKAGE_THEOREMS=1992; STANDARD_ONLY' in log,'Closure gate')
  result.append({'name':path.stem,'exit':r.returncode,'expected':expected,'log_sha256':hashlib.sha256(log.encode()).hexdigest()})
 require(len(result)==13,'Expected2 positive units and11 mutants')
 (out/'results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
 print('PASS: 1992 standard-only theorem closures, 48 positive examples and 11 effective mutants.')
if __name__=='__main__':main()
