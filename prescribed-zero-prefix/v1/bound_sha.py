from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent
def bound_sha(path):
 path=Path(path).resolve()
 if path.is_file():return hashlib.sha256(path.read_bytes()).hexdigest()
 rel=path.relative_to(H).as_posix()
 recorded=json.loads((H/'OMITTED-PROVENANCE-HASHES.json').read_text(encoding='utf-8'))
 if rel not in recorded:raise RuntimeError('Missing mathematical input: '+rel)
 return recorded[rel]
