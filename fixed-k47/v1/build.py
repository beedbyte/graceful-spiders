"""Verify or compile the fixed-k47 Lean source package."""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def verify():
    index = HERE / "SHA256SUMS.txt"
    need(index.is_file(), "checksum index missing")
    listed = {}
    for line in index.read_text(encoding="ascii").splitlines():
        digest, rel = line.split("  ", 1)
        need(rel not in listed and ".." not in Path(rel).parts, "invalid index path")
        listed[rel] = digest
    actual = {p.relative_to(HERE).as_posix() for p in HERE.rglob("*") if p.is_file()}
    need(actual == set(listed) | {"SHA256SUMS.txt"}, "package inventory mismatch")
    for rel, digest in listed.items():
        need(sha(HERE / rel) == digest, "package hash mismatch: " + rel)
    order = json.loads((HERE / "build-order.json").read_text(encoding="utf-8"))
    hashes = json.loads((HERE / "source-sha256.json").read_text(encoding="utf-8"))
    need(len(order) == 42 and len(set(order)) == 42 and set(order) == set(hashes), "module order")
    need({p.stem for p in (HERE / "source").glob("*.lean")} == set(order), "source set")
    seen = set()
    for module in order:
        data = (HERE / "source" / (module + ".lean")).read_bytes()
        need(hashlib.sha256(data).hexdigest() == hashes[module], "source map: " + module)
        for imported in re.findall(r"^import\s+([A-Za-z0-9_.]+)", data.decode("utf-8"), re.M):
            if imported in hashes:
                need(imported in seen, "forward local import: " + module)
            else:
                need(imported.split(".")[0] in {"Init", "Std", "Lean"}, "unpackaged import: " + imported)
        seen.add(module)
    return order, len(listed)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify hashes and imports only")
    parser.add_argument("--lean", default="lean", help="Lean 4.34.0 executable")
    parser.add_argument("--output", type=Path, help="new output directory outside this package")
    args = parser.parse_args()
    order, files = verify()
    if args.check:
        print(json.dumps({"status":"PASS", "sources":len(order), "indexed_files":files}))
        return
    need(args.output is not None, "--output is required for compilation")
    out = args.output.resolve()
    need(not out.exists(), "output directory already exists")
    need(not out.is_relative_to(HERE), "output directory must be outside this package")
    lean = shutil.which(args.lean) or str(Path(args.lean).resolve())
    version = subprocess.run([lean, "--version"], capture_output=True, text=True, encoding="utf-8", check=True).stdout
    need("4.34.0" in version, "Lean 4.34.0 required")
    out.mkdir(parents=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(out)
    env.pop("LEAN_SRC_PATH", None)
    rows = []
    for module in order:
        command = [lean, "-DwarningAsError=true", "-o", str(out / (module + ".olean")), module + ".lean"]
        proc = subprocess.run(command, cwd=HERE / "source", env=env, capture_output=True, text=True, encoding="utf-8")
        log = out / (module + ".log")
        log.write_text(proc.stdout + proc.stderr, encoding="utf-8")
        rows.append({"module":module, "source_sha256":sha(HERE / "source" / (module + ".lean")),
                     "exit_code":proc.returncode, "olean_sha256":sha(out / (module + ".olean")) if proc.returncode == 0 else None})
        (out / "build-record.json").write_text(json.dumps({"lean_version":version.strip(), "modules":rows}, indent=2) + "\n", encoding="utf-8")
        if proc.returncode:
            raise RuntimeError("Lean compile failed: " + module + "\n" + proc.stdout + proc.stderr)
    verify()
    print(json.dumps({"status":"PASS", "compiled_modules":len(rows), "indexed_files":files}))

if __name__ == "__main__":
    main()
