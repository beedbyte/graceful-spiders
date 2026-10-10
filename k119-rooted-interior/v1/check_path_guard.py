"""Offline regression tests for package output path protections."""
import sys
sys.dont_write_bytecode = True
import tempfile
from pathlib import Path
from package_paths import PACKAGE, guarded_output


def rejected(path):
    try:
        guarded_output(path)
    except (ValueError, OSError):
        return True
    return False


def main():
    assert rejected(PACKAGE / "would-be-output")
    assert rejected(PACKAGE / "source" / "nested-output")
    with tempfile.TemporaryDirectory() as td:
        base = Path(td)
        assert guarded_output(base / "fresh-output") == (base / "fresh-output").resolve()
        existing = base / "existing"
        existing.mkdir()
        assert rejected(existing)
        alias = base / "inside-alias"
        alias.symlink_to(PACKAGE, target_is_directory=True)
        assert rejected(alias / "child")
        dangling = base / "dangling-output"
        dangling.symlink_to(base / "absent-target")
        assert rejected(dangling)
    print("PASS: outside fresh path accepted; package, nested, existing, alias, and dangling symlink paths rejected")


if __name__ == "__main__":
    main()
