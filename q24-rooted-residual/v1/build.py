"""Verify this source-only package and build every Lean module from source.

Python 3.10+; Lean 4.34.0. Build objects and logs go only to --output.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

PACKAGE = Path(__file__).resolve().parent
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
DECLARATIONS = (
    'reverse_certificate', 'rooted_extreme', 'rooted_left', 'rooted_right',
    'terminal_parameters', 'terminal_four_s', 'terminal_four',
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(test: bool, explanation: str) -> None:
    if not test:
        raise RuntimeError(explanation)


def index_lines(path: Path) -> dict[str, str]:
    entries: dict[str, str] = {}
    for line in path.read_text(encoding='ascii').splitlines():
        expected, rel = line.split('  ', 1)
        require(rel not in entries, f'duplicate index entry: {rel}')
        require(len(expected) == 64, f'bad digest: {rel}')
        entries[rel] = expected
    return entries


def verify_package() -> tuple[list[str], dict[str, str]]:
    source_index = index_lines(PACKAGE / 'SOURCE-SHA256SUMS.txt')
    require(len(source_index) == 60, 'expected exactly 60 Lean sources')
    require(set(source_index) == {'source/' + p.name for p in (PACKAGE / 'source').glob('*.lean')},
            'source inventory mismatch')
    for rel, expected in source_index.items():
        require(digest(PACKAGE / rel) == expected, f'source hash mismatch: {rel}')
    require(source_index['source/Q24Rooted.lean'] ==
            '3920203716673dac6a87393e48043a78a94fc8e9fa1389eb66e3e4dee4f76024',
            'principal author source changed')

    provenance = json.loads((PACKAGE / 'provenance.json').read_text(encoding='utf-8'))
    for record in provenance['sources'] + provenance['evidence']:
        require(digest(PACKAGE / record['package_path']) == record['sha256'],
                f'provenance mismatch: {record["package_path"]}')
    require(len(provenance['sources']) == 60 and len(provenance['evidence']) == 15,
            'provenance inventory mismatch')

    payload_index = PACKAGE / 'SHA256SUMS.txt'
    if payload_index.exists():
        payloads = index_lines(payload_index)
        actual = {p.relative_to(PACKAGE).as_posix() for p in PACKAGE.rglob('*')
                  if p.is_file() and p.name != 'SHA256SUMS.txt'}
        require(set(payloads) == actual, 'package payload inventory mismatch')
        for rel, expected in payloads.items():
            require(digest(PACKAGE / rel) == expected, f'package hash mismatch: {rel}')

    order = json.loads((PACKAGE / 'build-order.json').read_text(encoding='utf-8'))
    require(len(order) == 60 and len(set(order)) == 60 and
            set(order) == {Path(p).stem for p in source_index}, 'build order mismatch')
    seen = set()
    for module in order:
        source = PACKAGE / 'source' / (module + '.lean')
        imports = re.findall(r'^import\s+([A-Za-z0-9_.]+)',
                             source.read_text(encoding='utf-8'), re.M)
        for dep in imports:
            if 'source/' + dep + '.lean' in source_index:
                require(dep in seen, f'bad import order: {module} imports {dep}')
            else:
                require(dep.split('.')[0] in {'Init', 'Std', 'Lean'},
                        f'unbundled import: {module} imports {dep}')
        seen.add(module)
    return order, source_index


def lean_run(lean: Path, source: Path, cwd: Path, env: dict[str, str],
             object_path: Path | None = None) -> tuple[int, str]:
    cmd = [str(lean), '-DwarningAsError=true']
    if object_path is not None:
        cmd += ['-o', str(object_path)]
    cmd += [str(source)]
    process = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True,
                             text=True, encoding='utf-8')
    return process.returncode, process.stdout + process.stderr


def build(lean: Path, output: Path, order: list[str]) -> None:
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    require('Lean (version 4.34.0,' in version, f'unsupported Lean: {version}')
    require(not output.is_relative_to(PACKAGE), '--output must be outside the source package')
    require(not output.exists(), '--output must be a new path')
    output.mkdir(parents=True)
    objects, logs = output / 'objects', output / 'logs'
    objects.mkdir()
    logs.mkdir()
    env = os.environ.copy()
    env['LEAN_PATH'] = str(objects)
    env.pop('LEAN_SRC_PATH', None)

    rows = []
    for number, module in enumerate(order, 1):
        path = PACKAGE / 'source' / (module + '.lean')
        code, log = lean_run(lean, path, PACKAGE / 'source', env,
                             objects / (module + '.olean'))
        (logs / (module + '.log')).write_text(log, encoding='utf-8')
        require(code == 0, f'Lean build failed in {module}; see output log')
        rows.append({'module': module, 'source_sha256': digest(path),
                     'object_sha256': digest(objects / (module + '.olean')),
                     'log_sha256': hashlib.sha256(log.encode('utf-8')).hexdigest()})
        print(f'[{number}/60] {module}', flush=True)
    require(len(list(objects.glob('*.olean'))) == 60, 'missing fresh object')

    query = PACKAGE / 'checks' / 'Query.lean'
    code, log = lean_run(lean, query, PACKAGE, env)
    (logs / 'Query.log').write_text(log, encoding='utf-8')
    query_log_sha256 = hashlib.sha256(log.encode('utf-8')).hexdigest()
    require(code == 0, 'positive theorem/triangle query failed')
    for name in DECLARATIONS:
        pattern = (r"'GracefulBoundary\.Q24Rooted\." + name +
                   r"' depends on axioms: \[([^\]]*)\]")
        match = re.search(pattern, log)
        require(match is not None, f'missing axiom closure: {name}')
        reported = {x.strip() for x in match.group(1).split(',')}
        require(reported == STANDARD_AXIOMS,
                f'nonstandard or missing axiom closure in {name}: {reported}')
    require('GracefulBoundary.Q24Rooted.terminal_four' in log,
            'exact theorem type not printed')

    negative = {}
    for name, reason in (('WrongRoot', 'is false'),
                         ('FalseOnto', 'Type mismatch'),
                         ('WrongDepth', 'Type mismatch')):
        code, log = lean_run(lean, PACKAGE / 'checks' / 'negative' / (name + '.lean'),
                             PACKAGE, env)
        (logs / (name + '.log')).write_text(log, encoding='utf-8')
        require(code != 0 and 'error:' in log and reason in log,
                f'ineffective semantic negative control: {name}')
        negative[name] = {'exit_code': code,
                          'log_sha256': hashlib.sha256(log.encode('utf-8')).hexdigest()}

    result = {'status': 'PASS', 'version': version, 'lean_sha256': digest(lean),
              'source_index_sha256': digest(PACKAGE / 'SOURCE-SHA256SUMS.txt'),
              'modules': rows, 'query_log_sha256': query_log_sha256,
              'negative': negative}
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': 'PASS', 'modules': len(rows),
                      'negative_controls': len(negative)}, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='verify package bytes and import order')
    parser.add_argument('--lean', type=Path, help='Lean 4.34.0 executable')
    parser.add_argument('--output', type=Path, help='fresh build directory outside package')
    args = parser.parse_args()
    order, source_index = verify_package()
    print(json.dumps({'package': 'q24-rooted-residual/v1', 'status': 'CHECK_PASS',
                      'sources': len(source_index), 'build_order': len(order)}, sort_keys=True))
    if args.check:
        return
    require(args.lean is not None and args.output is not None,
            'provide both --lean and --output, or use --check')
    build(args.lean.resolve(), args.output.resolve(), order)


if __name__ == '__main__':
    main()
