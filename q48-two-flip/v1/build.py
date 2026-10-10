#!/usr/bin/env python3
"""Verify and freshly build this source package; Python standard library only."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

PACKAGE = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify():
    entries = {}
    for line in (PACKAGE / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
        h, name = line.split("  ", 1)
        require(re.fullmatch(r"[0-9a-f]{64}", h), "Invalid checksum")
        require(name not in entries, "Duplicate manifest entry: " + name)
        target = (PACKAGE / name).resolve()
        require(PACKAGE in target.parents, "Manifest path outside package")
        require(target.is_file() and digest(target) == h, "Checksum mismatch: " + name)
        entries[name] = h
    actual = {p.relative_to(PACKAGE).as_posix() for p in PACKAGE.rglob("*") if p.is_file()}
    require(actual == set(entries) | {"SHA256SUMS.txt"}, "Unlisted or missing package files")
    order = json.loads((PACKAGE / "build-order.json").read_text(encoding="utf-8"))
    hashes = json.loads((PACKAGE / "source-sha256.json").read_text(encoding="utf-8"))
    require(len(order) == len(set(order)) == len(hashes) == 36, "Expected 36 modules")
    require(set(order) == set(hashes), "Source/build-order mismatch")
    seen = set()
    for module in order:
        require(re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", module), "Invalid module name")
        path = PACKAGE / "source" / (module + ".lean")
        require(digest(path) == hashes[module], "Source map mismatch: " + module)
        for dep in re.findall(r"^import\s+([\w.]+)\s*$", path.read_text(encoding="utf-8"), re.M):
            require(dep in seen or dep.split(".")[0] in {"Init", "Std", "Lean"},
                    "Unresolved or out-of-order import: " + module + " -> " + dep)
        seen.add(module)
    return order, entries

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Verify without compiling")
    parser.add_argument("--lean", default="lean", help="Lean 4.34.0 executable")
    parser.add_argument("--output", help="New output directory outside this package")
    args = parser.parse_args()
    order, entries = verify()
    if args.check:
        require(args.output is None, "--check does not use --output")
        print(json.dumps({"status": "PASS", "sources": len(order), "checked_files": len(entries)}, sort_keys=True))
        return
    require(args.output is not None, "Supply --output or use --check")
    output = Path(args.output).expanduser().resolve()
    require(output != PACKAGE and PACKAGE not in output.parents, "Output must be outside package")
    require(not output.exists(), "Output directory already exists; choose a fresh path")
    executable = shutil.which(args.lean)
    require(executable is not None, "Lean executable not found")
    executable = str(Path(executable).resolve())
    version = subprocess.run([executable, "--version"], capture_output=True, text=True, encoding="utf-8")
    require(version.returncode == 0 and re.search(r"version 4\.34\.0(?:,|\))", version.stdout),
            "This package requires Lean 4.34.0")
    output.mkdir(parents=True, exist_ok=False)
    logs = output / "logs"
    logs.mkdir()
    env = os.environ.copy()
    env["LEAN_PATH"] = str(output)
    env.pop("LEAN_SRC_PATH", None)
    record = {"status": "RUNNING", "toolchain": version.stdout.strip(),
              "lean_sha256": digest(Path(executable)),
              "package_manifest_sha256": digest(PACKAGE / "SHA256SUMS.txt"), "modules": []}
    def save():
        (output / "build-record.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    save()
    for i, module in enumerate(order, 1):
        obj = output / (module + ".olean")
        cmd = [executable, "-DwarningAsError=true", "-o", str(obj), module + ".lean"]
        start = time.monotonic()
        result = subprocess.run(cmd, cwd=PACKAGE / "source", env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
        (logs / (module + ".log")).write_text(result.stdout, encoding="utf-8")
        record["modules"].append({"module": module, "command": cmd, "exit": result.returncode,
                                  "seconds": time.monotonic() - start,
                                  "object_sha256": digest(obj) if obj.exists() else None})
        if result.returncode:
            record["status"] = "FAIL"
            save()
            raise RuntimeError("Lean rejected " + module + "; inspect its log")
        save()
        print(str(i) + "/36 " + module, flush=True)
    verify()
    record["status"] = "PASS"
    save()
    print("PASS: all 36 modules freshly compiled; package hashes unchanged.")

if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print("ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
