"""Explicit constructive witnesses. No search, solver or third-party packages.

Vertices: 'c', ('a', arm_index, depth), ('p', leaf_index).
"""
import json
from pathlib import Path

CERTS = json.loads(Path(__file__).with_name('certificates.json').read_text())['certificates']


def center_zero(k, n, m):
    assert k >= 1 and n >= 0 and m >= 0
    f = {'c': 0}
    for i in range(n):
        for j in range(1, k + 1):
            f['a', i, j] = (n - i) * k - (j - 1) // 2 if j % 2 else i * k + j // 2
    f.update({('p', j): n * k + j + 1 for j in range(m)})
    return f


def near_center_path(k):
    assert k >= 3 and k % 2
    r = (k - 1) // 2
    left = [4 * r + 2 - j // 2 if j % 2 else j // 2 - 1 for j in range(1, k + 1)]
    right = [2 * r + 1 + j // 2 if j % 2 else 2 * r - j // 2 for j in range(1, k + 1)]
    return list(reversed(left)) + [2 * r] + right


def amalgamate(k, n, m, path):
    assert n >= 2 and len(path) == 2 * k + 1
    alpha = path[k]
    g = center_zero(k, n - 2, m)
    size = (n - 2) * k + m
    f = {}
    for v, x in g.items():
        new_v = ('a', v[1] + 2, v[2]) if isinstance(v, tuple) and v[0] == 'a' else v
        f[new_v] = x + alpha
    for a, indices in ((0, range(k - 1, -1, -1)), (1, range(k + 1, 2 * k + 1))):
        for j, ix in enumerate(indices, 1):
            x = path[ix]
            f['a', a, j] = x if x <= alpha else x + size
    return f


def leaf_zero(k, n, m, short=False):
    if short:
        assert m >= 1
        f = center_zero(k, n, m - 1)
        q = n * k + m
        f = {v: q - x for v, x in f.items()}
        f['p', m - 1] = 0
        return f
    f = center_zero(k, n - 1, m)
    for j in range(1, k + 1):
        q = len(f)
        f = {v: q - x for v, x in f.items()}
        f['a', n - 1, j] = 0
    return f


def complement(f):
    q = len(f) - 1
    return {v: q - x for v, x in f.items()}


def representative(k, n, m, role):
    assert k in (3, 5, 7, 9) and n >= 2 and m >= 0
    if role == 'center':
        return center_zero(k, n, m)
    if role == 'leaf':
        return leaf_zero(k, n, m, True)
    depth = int(role)
    if depth in (k - 1, k):
        f = leaf_zero(k, n, m)
        return f if depth == k else complement(f)
    if depth in (1, 2):
        f = amalgamate(k, n, m, near_center_path(k))
        return complement(f) if depth == 1 else f
    for cert in CERTS:
        if cert['k'] != k:
            continue
        if depth in (cert['zero_depth'], cert['max_depth']):
            f = amalgamate(k, n, m, cert['path'])
            return f if depth == cert['zero_depth'] else complement(f)
    raise ValueError((k, depth))


def prescribed_zero(k, n, m, target):
    """Construct a labeling with zero at an exact requested named vertex."""
    if target == 'c':
        return representative(k, n, m, 'center')
    role = 'leaf' if target[0] == 'p' else target[2]
    f = representative(k, n, m, role)
    old = next(v for v, x in f.items() if x == 0)
    if old == target:
        return f
    if target[0] == 'p':
        assert 0 <= target[1] < m
        f[old], f[target] = f[target], f[old]
        return f
    assert target[0] == 'a' and 0 <= target[1] < n and old[2] == target[2]
    for j in range(1, k + 1):
        u, v = ('a', old[1], j), ('a', target[1], j)
        f[u], f[v] = f[v], f[u]
    return f


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('k', type=int, choices=(3, 5, 7, 9))
    parser.add_argument('n', type=int)
    parser.add_argument('m', type=int)
    parser.add_argument('role', help='center, leaf, or long-arm depth')
    args = parser.parse_args()
    print(json.dumps({str(v): x for v, x in representative(args.k, args.n, args.m, args.role).items()}, indent=2))
