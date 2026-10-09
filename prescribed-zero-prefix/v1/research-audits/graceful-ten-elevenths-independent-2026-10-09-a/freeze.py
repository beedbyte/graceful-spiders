"""Freeze exact read-only input bindings and both independent replay modes."""
import json,hashlib,subprocess,sys
from pathlib import Path
H=Path(__file__).resolve().parent
W=H.parent.parent
AUTHOR=H.parent/'graceful-ten-elevenths-global-2026-10-09-a'
def digest(p):
    raw=p.read_bytes();return {'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)}
bindings={}
def bind(p):
    bindings[str(p.relative_to(W)).replace('\\','/')]=digest(p)
historical=json.loads((AUTHOR/'inputs.json').read_text())
for rel,expected in historical.items():
    p=W/rel
    if digest(p)['sha256']!=expected:raise ValueError('author historical binding '+rel)
    bind(p)
for p in AUTHOR.iterdir():
    if p.is_file():bind(p)
original=H.parent/'graceful-reverse-complement-independent-2026-10-09-a'/'audit.py'
if (H/'core_graph.py').read_bytes()!=original.read_bytes():raise ValueError('independent graph code provenance')
bind(original)
for name in ['seeds.json','small-seeds.json','old-data.json','gadget30.json','report.md','manifest.json']:
    bind(H.parent/'graceful-compatible-seed-prefix-2026-10-09-a'/name)
for name in ['graceful-even-core-shell-2026-10-09-a','graceful-even-shell-independent-2026-10-09-a']:
    for file in ['report.md','manifest.json']:bind(H.parent/name/file)
manifest_counts={}
for rel in list(bindings):
    if not rel.endswith('/manifest.json'):continue
    path=W/rel;data=json.loads(path.read_text(encoding='utf-8-sig'))
    entries=data.get('files',data.get('payloads',data))
    if isinstance(entries,list):entries={v.get('path',v.get('file')):v for v in entries}
    count=0
    for name,v in entries.items():
        if not isinstance(v,dict) or 'sha256' not in v:continue
        observed=digest(path.parent/name)
        if observed['sha256']!=v['sha256'] or ('bytes' in v and observed['bytes']!=v['bytes']):raise ValueError('manifest member '+str(path.parent/name))
        count+=1
    manifest_counts[rel]=count
(H/'source-inputs.json').write_text(json.dumps({'files':bindings,'manifest_payload_counts':manifest_counts},sort_keys=True,indent=2)+'\n',encoding='utf-8')
for source,stem in [('audit.py','audit'),('check_author.py','author')]:
    normal=subprocess.check_output([sys.executable,'-B',str(H/source)])
    optimized=subprocess.check_output([sys.executable,'-B','-O',str(H/source)])
    if normal!=optimized:raise ValueError('mode mismatch '+source)
    (H/(stem+'-normal.json')).write_bytes(normal)
    (H/(stem+'-optimized.json')).write_bytes(optimized)
for rel,expected in bindings.items():
    if digest(W/rel)!=expected:raise ValueError('input drift '+rel)
manifest={p.name:digest(p) for p in sorted(H.iterdir()) if p.is_file() and p.name not in ['manifest.json','SHA256SUMS.txt']}
(H/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n',encoding='utf-8')
(H/'SHA256SUMS.txt').write_text(''.join(v['sha256']+'  '+name+'\n' for name,v in manifest.items()),encoding='utf-8')
print(json.dumps({'report':digest(H/'report.md'),'manifest':digest(H/'manifest.json'),'bound_inputs':len(bindings),'manifest_payload_counts':manifest_counts},sort_keys=True,indent=2))
