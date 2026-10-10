"""Shared safe package-path checks (no filesystem writes)."""
import os
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent


def guarded_output(raw_path):
    raw = Path(raw_path).expanduser()
    # Inspect the caller's lexical path before resolve(), which erases dangling links.
    if os.path.lexists(raw) and raw.is_symlink():
        raise ValueError("output destination is a symlink")
    resolved = raw.resolve(strict=False)
    if resolved == PACKAGE or PACKAGE in resolved.parents:
        raise ValueError("output destination must be outside the package")
    if os.path.lexists(raw):
        raise ValueError("output destination must not already exist")
    return resolved
