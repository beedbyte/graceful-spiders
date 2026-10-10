"""Rebuild all pinned Lean sources and execute positive/negative controls."""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

sys.dont_write_bytecode = True
from package_paths import PACKAGE, guarded_output

LEAN_SHA = "a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PASS_CHECKS = {"Support", "Positive", "WholeClosure"}
MUTANTS = ["AllInteriorForR2", "Center0", "FalseOnto", "NoRootZero", "OmittedComplement", "OutsideFamily", "SameLabelBoth", "Seed12OldState", "Seed34OldMidpoint", "Tip119", "WrongArm", "WrongClosedLength", "WrongExtreme", "WrongMidpoint", "WrongOffset", "ZeroIteration"]


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def pins(path):
    out = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        digest, rel = line.split("  ", 1)
        if rel in out:
            raise ValueError(f"duplicate checksum entry: {rel}")
        out[rel] = digest
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", required=True, type=Path)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    output = guarded_output(args.output)
    lean = args.lean.resolve(strict=True)
    if not lean.is_file() or sha(lean) != LEAN_SHA:
        raise SystemExit("Lean executable missing or SHA256 does not match pinned Lean 4.34.0")
    source_pins = pins(PACKAGE / "SOURCE-SHA256SUMS.txt")
    check_pins = pins(PACKAGE / "CHECK-SHA256SUMS.txt")
    for mapping in (source_pins, check_pins):
        for rel, digest in mapping.items():
            if sha(PACKAGE / rel) != digest:
                raise SystemExit(f"package integrity failure: {rel}")
    order = json.loads((PACKAGE / "module-order.json").read_text(encoding="utf-8"))
    if len(order) != 68 or len(set(order)) != 68 or {f"source/{x}.lean" for x in order} != set(source_pins):
        raise SystemExit("module order and source index do not match 68 modules")
    output.mkdir(parents=True, exist_ok=False)
    objects, logs = output / "objects", output / "logs"
    objects.mkdir(); logs.mkdir()
    env = os.environ.copy()
    env["LEAN_PATH"] = str(objects)
    build_rows = []
    for module in order:
        start = time.monotonic()
        proc = subprocess.run([str(lean), "-DwarningAsError=true", "-o", str(objects / (module + ".olean")), module + ".lean"], cwd=PACKAGE / "source", env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (logs / (module + ".log")).write_bytes(proc.stdout)
        row = {"module": module, "exit": proc.returncode, "source_sha256": sha(PACKAGE / "source" / (module + ".lean")), "object_sha256": sha(objects / (module + ".olean")) if proc.returncode == 0 else None, "seconds": round(time.monotonic() - start, 3)}
        build_rows.append(row)
        (output / "build-results.json").write_text(json.dumps(build_rows, indent=2) + "\n", encoding="utf-8")
        print(f"build {module}: {proc.returncode}", flush=True)
        if proc.returncode:
            raise SystemExit(f"Lean build failed: {module}")
    check_rows = []
    closure_rows = []
    for name in ["Support", "Positive", "WholeClosure"] + MUTANTS:
        start = time.monotonic()
        command = [str(lean), "-DwarningAsError=true"]
        if name in {"Support", "Positive"}:
            command += ["-o", str(objects / (name + ".olean"))]
        command += [name + ".lean"]
        proc = subprocess.run(command, cwd=PACKAGE / "checks", env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = proc.stdout.decode("utf-8", errors="replace")
        (logs / (name + ".log")).write_bytes(proc.stdout)
        expected_pass = name in PASS_CHECKS
        if (proc.returncode == 0) != expected_pass:
            raise SystemExit(f"unexpected check result: {name}, exit {proc.returncode}")
        if not expected_pass:
            bad = ["unknown identifier", "unknown module", "does not exist", "maximum recursion", "maximum number of heartbeats"]
            if any(s in log.lower() for s in bad) or not any(s in log for s in ["Type mismatch", "type mismatch", "decide", "unsolved goals"]):
                raise SystemExit(f"negative control was not a semantic rejection: {name}")
        if name == "WholeClosure":
            for line in log.splitlines():
                if line.startswith("CLOSURE|"):
                    _, theorem, module, axioms = line.split("|", 3)
                    axset = set(re.findall(r"[A-Za-z][A-Za-z0-9_.]*", axioms))
                    if not axset <= ALLOWED_AXIOMS:
                        raise SystemExit(f"unexpected axiom dependency: {theorem}: {axset}")
                    closure_rows.append({"name": theorem, "module": module, "axioms": sorted(axset)})
            theorem_modules = {row["module"] for row in closure_rows}
            expected_modules = set(order) - {"Q24Arrays", "Q54Arrays"}
            if len(closure_rows) != 2809 or theorem_modules != expected_modules:
                raise SystemExit(f"closure census mismatch: {len(closure_rows)} declarations / {len(theorem_modules)} modules")
            (output / "axiom-inventory.json").write_text(json.dumps(closure_rows, indent=2) + "\n", encoding="utf-8")
        check_rows.append({"name": name, "exit": proc.returncode, "expected": "pass" if expected_pass else "semantic rejection", "source_sha256": sha(PACKAGE / "checks" / (name + ".lean")), "seconds": round(time.monotonic() - start, 3)})
        (output / "check-results.json").write_text(json.dumps(check_rows, indent=2) + "\n", encoding="utf-8")
        print(f"check {name}: {proc.returncode}", flush=True)
    summary = {"lean_version": subprocess.check_output([str(lean), "--version"], text=True).strip(), "lean_sha256": LEAN_SHA, "modules_compiled": len(build_rows), "closure_count": len(closure_rows), "closure_modules": len(set(x["module"] for x in closure_rows)), "allowed_axioms": sorted(ALLOWED_AXIOMS), "checks": len(check_rows), "semantic_mutants_rejected": len(MUTANTS), "status": "PASS"}
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
