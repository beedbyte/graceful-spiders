"""Verify source/check payload hashes and the exact 68-module order."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_sums(path):
    result = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        digest, name = line.split("  ", 1)
        if name in result:
            raise ValueError(f"duplicate hash row: {name}")
        result[name] = digest
    return result


def verify(kind, sums_name):
    expected = read_sums(ROOT / sums_name)
    actual_files = sorted(p for p in (ROOT / kind).rglob("*") if p.is_file())
    actual = {p.relative_to(ROOT).as_posix(): sha(p) for p in actual_files}
    if actual != expected:
        raise SystemExit(f"{kind} inventory/hash mismatch")
    return len(actual)


def main():
    source_n = verify("source", "SOURCE-SHA256SUMS.txt")
    check_n = verify("checks", "CHECK-SHA256SUMS.txt")
    order = json.loads((ROOT / "module-order.json").read_text(encoding="utf-8"))
    if len(order) != 68 or len(set(order)) != 68 or source_n != 68:
        raise SystemExit("expected 68 unique ordered source modules")
    if {f"source/{name}.lean" for name in order} != set(read_sums(ROOT / "SOURCE-SHA256SUMS.txt")):
        raise SystemExit("module order/source inventory mismatch")
    names = {p.stem for p in (ROOT / "checks").glob("*.lean")}
    expected = {"Support", "Positive", "WholeClosure", "AllInteriorForR2", "Center0", "FalseOnto", "NoRootZero", "OmittedComplement", "OutsideFamily", "SameLabelBoth", "Seed12OldState", "Seed34OldMidpoint", "Tip119", "WrongArm", "WrongClosedLength", "WrongExtreme", "WrongMidpoint", "WrongOffset", "ZeroIteration"}
    if names != expected or check_n != 19:
        raise SystemExit("check inventory mismatch")
    print(f"PASS: {source_n} source modules and {check_n} check modules match exact pins")


if __name__ == "__main__":
    main()
