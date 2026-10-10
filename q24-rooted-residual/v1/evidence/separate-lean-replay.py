from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(r'E:\KI-Research')
AUDITS = ROOT / 'research-audits'
Q24 = AUDITS / 'graceful-q24-zero-order-formal-2026-10-10-a'
ROOTED = AUDITS / 'graceful-k71-rooted-residual-formal-2026-10-10-a'
AUTHOR = AUDITS / 'graceful-q24-rooted-residual-lean-2026-10-10-a'
OUT = AUDITS / 'graceful-q24-rooted-residual-independent-replay-2026-10-10-a'
LEAN = Path(r'C:\Users\Jordi\AppData\Local\Temp\rule30-lean-4.34.0\lean-4.34.0-windows\bin\lean.exe')
PINS = {
    ROOTED / 'SOURCE-SHA256SUMS.txt': '45b2c193ce997f0d150dd90be66c13dff6daf38f666671dd887d177d3d775eba',
    Q24 / 'SOURCE-SHA256SUMS.txt': 'c55f3f4af89434b2ab9439d5391237834b4f767a81a19daab3b26123a47db66d',
    AUTHOR / 'SOURCE-SHA256SUMS.txt': '329f68dd57f383cf1bc420bfc7048cea06d9d70774ff9b55c3194e7152e086f6',
    AUTHOR / 'report.md': '7fe5063608bdb1ebf32ce5574ea52e7d956cf6ddccc55e073ce92490b648e5b0',
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def need(test: bool, message: str) -> None:
    if not test:
        raise RuntimeError(message)


def read_index(packet: Path) -> dict[str, tuple[Path, str]]:
    index = packet / 'SOURCE-SHA256SUMS.txt'
    out = {}
    for line in index.read_text(encoding='ascii').splitlines():
        h, rel = line.split('  ', 1)
        source = packet / rel
        need(sha(source.read_bytes()) == h, f'index mismatch: {source}')
        name = source.name
        need(name not in out, f'duplicate module name: {name}')
        out[name] = source, h
    return out


for path, pin in PINS.items():
    need(sha(path.read_bytes()) == pin, f'packet pin mismatch: {path}')

rooted = read_index(ROOTED)
q24 = read_index(Q24)
author = read_index(AUTHOR)
need(len(rooted) == 58 and len(q24) == 34, 'unexpected predecessor source count')
need(set(author) == {'Q24Rooted.lean', 'checks/Closures.lean', 'checks/TriangleCase.lean',
                     'mutants/WrongRoot.lean', 'mutants/FalseOnto.lean',
                     'mutants/WrongDepth.lean'} or 'Q24Rooted.lean' in author,
     'missing author theorem source')

sources = dict(rooted)
for name, (path, h) in q24.items():
    if name in sources:
        need(sources[name][1] == h, f'incompatible shared source: {name}')
    else:
        sources[name] = path, h
need(len(sources) == 59 and 'Q24Terminal.lean' in sources, 'unexpected merged predecessor set')
sources['Q24Rooted.lean'] = AUTHOR / 'Q24Rooted.lean', author['Q24Rooted.lean'][1]

srcdir, objdir, logdir = (OUT / 'copied-source', OUT / 'fresh-objects', OUT / 'logs')
need(not srcdir.exists() and not objdir.exists(), 'fresh output directories already exist')
srcdir.mkdir()
objdir.mkdir()
logdir.mkdir(exist_ok=True)
for name, (source, h) in sources.items():
    data = source.read_bytes()
    need(sha(data) == h, f'source byte pin mismatch: {source}')
    (srcdir / name).write_bytes(data)
    need(sha((srcdir / name).read_bytes()) == h, f'copy mismatch: {name}')

imports = {}
for name in sources:
    module = Path(name).stem
    deps = re.findall(r'^import\s+([A-Za-z0-9_.]+)',
                      (srcdir / name).read_text(encoding='utf-8'), re.M)
    imports[module] = []
    for dep in deps:
        if dep + '.lean' in sources:
            imports[module].append(dep)
        else:
            need(dep.split('.')[0] in {'Init', 'Std', 'Lean'},
                 f'nonstandard external import {dep} in {name}')

order, done = [], set()
while len(order) < len(sources):
    ready = sorted(m for m in imports if m not in done and all(d in done for d in imports[m]))
    need(bool(ready), 'unresolved dependency graph')
    order.extend(ready)
    done.update(ready)
need('Q24Rooted' in order, 'principal source missing from dependency order')

version = subprocess.check_output([str(LEAN), '--version'], text=True).strip()
need('4.34.0' in version, 'unexpected Lean version')
env = os.environ.copy()
env['LEAN_PATH'] = str(objdir)
env.pop('LEAN_SRC_PATH', None)
rows = []
start = time.time()
for i, module in enumerate(order, 1):
    cmd = [str(LEAN), '-DwarningAsError=true', '-o', str(objdir / f'{module}.olean'),
           f'{module}.lean']
    result = subprocess.run(cmd, cwd=srcdir, env=env, capture_output=True,
                            text=True, encoding='utf-8')
    log = result.stdout + result.stderr
    (logdir / f'{module}.log').write_text(log, encoding='utf-8')
    rows.append({'module': module, 'source_sha256': sources[f'{module}.lean'][1],
                 'exit_code': result.returncode, 'log_sha256': sha(log.encode('utf-8'))})
    print(f'[{i}/{len(order)}] {module}: {result.returncode}', flush=True)
    if result.returncode:
        raise RuntimeError(f'Lean failed at {module}:\n{log}')

output = {'status': 'PASS', 'lean_version': version,
          'lean_sha256': sha(LEAN.read_bytes()), 'source_count': len(sources),
          'olean_count': len(list(objdir.glob('*.olean'))),
          'build_seconds': round(time.time() - start, 2),
          'author_source_sha256': author['Q24Rooted.lean'][1],
          'source_order': order, 'modules': rows}
(OUT / 'build-result.json').write_text(json.dumps(output, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: output[k] for k in ('status', 'source_count', 'olean_count',
                                        'build_seconds', 'lean_sha256')}, sort_keys=True))
