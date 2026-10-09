"""Capture two independent audit modes and bind immutable source inputs."""
import json,hashlib,subprocess,sys
from pathlib import Path
H=Path(__file__).resolve().parent;W=H.parent.parent
AUTHOR=H.parent/'graceful-q10-gap-fill-beyond-d7-2026-10-09-a'
def digest(p):
    raw=p.read_bytes();return {'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)}
bindings={}
def bind(p):bindings[str(p.relative_to(W)).replace('\\','/')]=digest(p)
for rel,expected in json.loads((AUTHOR/'inputs.json').read_text()).items():
    p=W/rel
    if digest(p)['sha256']!=expected:raise ValueError('input hash '+rel)
    bind(p)
for p in AUTHOR.iterdir():
    if p.is_file():bind(p)
original=H.parent/'graceful-reverse-complement-independent-2026-10-09-a'/'audit.py'
if original.read_bytes()!=(H/'core_graph.py').read_bytes():raise ValueError('own graph code provenance')
bind(original)
for name in ['seeds.json','small-seeds.json','old-data.json','gadget30.json','report.md','manifest.json']:
    bind(H.parent/'graceful-compatible-seed-prefix-2026-10-09-a'/name)
counts={}
for rel in list(bindings):
    if not rel.endswith('/manifest.json'):continue
    path=W/rel;data=json.loads(path.read_text(encoding='utf-8-sig'))
    entries=data.get('files',data.get('payloads',data))
    if isinstance(entries,list):entries={x.get('path',x.get('file')):x for x in entries}
    count=0
    for name,item in entries.items():
        if not isinstance(item,dict) or 'sha256' not in item:continue
        observed=digest(path.parent/name)
        if observed['sha256']!=item['sha256'] or ('bytes' in item and observed['bytes']!=item['bytes']):raise ValueError('payload '+str(path.parent/name))
        count+=1
    counts[rel]=count
(H/'source-inputs.json').write_text(json.dumps({'files':bindings,'verified_manifest_payloads':counts},sort_keys=True,indent=2)+'\n',encoding='utf-8')
normal=subprocess.check_output([sys.executable,'-B',str(H/'audit.py')])
optimized=subprocess.check_output([sys.executable,'-B','-O',str(H/'audit.py')])
if normal!=optimized:raise ValueError('mode mismatch')
for rel,expected in bindings.items():
    if digest(W/rel)!=expected:raise ValueError('input drift '+rel)
(H/'normal-results.json').write_bytes(normal)
(H/'optimized-results.json').write_bytes(optimized)
manifest={p.name:digest(p) for p in sorted(H.iterdir()) if p.is_file() and p.name not in ['manifest.json','SHA256SUMS.txt']}
(H/'manifest.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n',encoding='utf-8')
(H/'SHA256SUMS.txt').write_text(''.join(v['sha256']+'  '+name+'\n' for name,v in manifest.items()),encoding='utf-8')
print(json.dumps({'report':digest(H/'report.md'),'manifest':digest(H/'manifest.json'),'bound_inputs':len(bindings),'verified_manifest_payloads':counts},sort_keys=True,indent=2))
