"""Resolved destination guards for the portable Lean build."""
from pathlib import Path
import os

def _inside(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
        return True
    except ValueError:
        return False

def validated_destinations(package_root, requested_output):
    package = Path(package_root).resolve()
    # Derive the three caller-visible names before resolving anything. Checking
    # lexists first catches dangling symlinks that resolve() would erase.
    requested = Path(requested_output).expanduser().absolute()
    requested_logs = requested.parent / (requested.name + "-logs")
    requested_results = requested.parent / (requested.name + "-results.json")
    lexical = (("output", requested), ("logs", requested_logs), ("results", requested_results))
    for label, path in lexical:
        if os.path.lexists(path) or path.is_symlink():
            raise FileExistsError(f"{label} destination already exists or is a symlink")
    output = requested.resolve()
    logs = requested_logs.resolve()
    results = requested_results.resolve()
    for label, path in (("output", output), ("logs", logs), ("results", results)):
        if _inside(path, package):
            raise ValueError(f"{label} destination resolves inside the package")
    # Repeat existence checks on canonical destinations (including all aliases).
    for label, path in (("output", output), ("logs", logs), ("results", results)):
        if os.path.lexists(path) or path.is_symlink():
            raise FileExistsError(f"{label} destination already exists")
    return output, logs, results
