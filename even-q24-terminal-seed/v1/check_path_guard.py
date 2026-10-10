"""Offline regression controls for output containment and collision guards."""
from pathlib import Path
import os, sys, tempfile
sys.dont_write_bytecode = True
from path_guard import validated_destinations

def rejected(pkg, out):
    try: validated_destinations(pkg,out)
    except (ValueError,FileExistsError): return True
    return False

with tempfile.TemporaryDirectory(prefix="q24-seed-guard-") as td:
    root=Path(td); pkg=root/"package"; pkg.mkdir(); child=pkg/"inside"; child.mkdir()
    assert rejected(pkg,pkg), "package root accepted"
    assert rejected(pkg,pkg/"absent"), "package child accepted"
    assert rejected(pkg,child/"deeper"/"out"), "nested child accepted"
    outside=root/"outside"/"objects"
    got=validated_destinations(pkg,outside)
    assert got[0]==outside.resolve() and all(not p.exists() for p in got)
    # Existing output, sibling log, and sibling result destinations all fail closed.
    ext=root/"collision"; ext.mkdir(); assert rejected(pkg,ext), "existing output accepted"
    ext2=root/"log-collision"; (root/"logs-logs").mkdir()
    assert rejected(pkg,root/"logs"), "existing sibling logs accepted"
    (root/"result-results.json").write_text("reserved")
    assert rejected(pkg,root/"result"), "existing sibling result accepted"
    # A path outside lexically but redirected by a symlink into the package is rejected.
    alias=root/"alias"
    try:
        alias.symlink_to(pkg,target_is_directory=True)
    except (OSError,NotImplementedError) as e:
        raise SystemExit("symlink guard test unavailable: "+str(e))
    assert rejected(pkg,alias/"child"/"out"), "symlink-resolved package child accepted"
    # Dangling symlinks must be rejected before resolve() can erase their names.
    dangling=root/"missing-target"
    for out, link in ((root/"dangling-out",root/"dangling-out"),
                      (root/"dangling-log",root/"dangling-log-logs"),
                      (root/"dangling-result",root/"dangling-result-results.json")):
        link.symlink_to(dangling)
        assert rejected(pkg,out), "dangling output/log/result symlink accepted: "+str(link.name)
print("PATH_GUARD_CONTROLS_PASS")
