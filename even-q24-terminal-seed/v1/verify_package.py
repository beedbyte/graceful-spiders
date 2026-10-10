from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
rows=json.loads((root/"PAYLOAD-SHA256.json").read_text(encoding="utf-8"))
for row in rows:
    p=root/row["path"]
    if not p.is_file(): raise SystemExit(f"missing: {row['path']}")
    b=p.read_bytes()
    if len(b)!=row["bytes"] or hashlib.sha256(b).hexdigest()!=row["sha256"]:
        raise SystemExit(f"hash/size mismatch: {row['path']}")
print(f"PAYLOAD_INTEGRITY_PASS files={len(rows)}")
