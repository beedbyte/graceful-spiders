from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess

OUT = Path(r'E:\KI-Research\research-audits\graceful-q24-rooted-residual-independent-replay-2026-10-10-a')
LEAN = Path(r'C:\Users\Jordi\AppData\Local\Temp\rule30-lean-4.34.0\lean-4.34.0-windows\bin\lean.exe')
OBJ = OUT / 'fresh-objects'
env = os.environ.copy()
env['LEAN_PATH'] = str(OBJ)
env.pop('LEAN_SRC_PATH', None)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(path: Path) -> dict:
    result = subprocess.run([str(LEAN), '-DwarningAsError=true', str(path)],
                            cwd=OUT, env=env, capture_output=True,
                            text=True, encoding='utf-8')
    log = result.stdout + result.stderr
    (OUT / (path.stem + '.log')).write_text(log, encoding='utf-8')
    return {'file': str(path.relative_to(OUT)).replace('\\', '/'),
            'source_sha256': sha(path.read_bytes()), 'exit_code': result.returncode,
            'log_sha256': sha(log.encode('utf-8')), 'log': log}


query = run(OUT / 'Query.lean')
if query['exit_code']:
    raise RuntimeError('positive query failed:\n' + query['log'])
expected = ['GracefulBoundary.Q24Rooted.terminal_four',
            'GracefulBoundary.Rooted71.triangle_not_onto',
            'propext', 'Classical.choice', 'Quot.sound']
for needle in expected:
    if needle not in query['log']:
        raise RuntimeError(f'missing query evidence: {needle}')

mutants = [run(OUT / 'mutants' / (name + '.lean'))
           for name in ('WrongRoot', 'FalseOnto', 'WrongDepth')]
for row in mutants:
    if row['exit_code'] == 0 or 'error:' not in row['log']:
        raise RuntimeError('ineffective mutant: ' + row['file'])

result = {'status': 'PASS', 'query': {k: v for k, v in query.items() if k != 'log'},
          'mutants': [{k: v for k, v in row.items() if k != 'log'} for row in mutants]}
(OUT / 'control-result.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(json.dumps(result, sort_keys=True))
