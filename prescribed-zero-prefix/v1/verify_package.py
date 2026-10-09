"""Verify selected immutable sources and current package, without compilation."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent
def need(x,m):
 if not x:raise RuntimeError(m)
manifest=json.loads((H/'PACKAGE-MANIFEST.json').read_text(encoding='utf-8'))
for row in manifest['files']:
 p=(H/row['path']).resolve();need(p.is_relative_to(H.resolve()),'unsafe manifest path')
 need(p.is_file() and p.stat().st_size==row['bytes'],'missing/size: '+row['path'])
 need(hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],'hash: '+row['path'])
need(not any(Path(row['path']).suffix=='.olean' for row in manifest['files']),'unexpected bundled compiler object')
print('PASS selected package hashes; original historical manifest omission lists remain explicit.')
