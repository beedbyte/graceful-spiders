"""Standard-library checker; graph and difference checks independent of search.

Uses the construction module as a witness producer, never trusts its invariants.
Finite tests supplement the unbounded proof in proof.md.
"""
import json
from collections import Counter
from pathlib import Path
import construct


def graph(k, n, m):
    verts, edges = ['c'], []
    for arm in range(n):
        previous = 'c'
        for depth in range(1, k + 1):
            v = ('a', arm, depth)
            verts.append(v)
            edges.append((previous, v))
            previous = v
    for leaf in range(m):
        v = ('p', leaf)
        verts.append(v)
        edges.append(('c', v))
    return verts, edges


def check(k, n, m, f, target=None):
    verts, edges = graph(k, n, m)
    q = len(edges)
    assert set(f) == set(verts)
    assert Counter(f.values()) == Counter(range(q + 1))
    assert Counter(abs(f[u] - f[v]) for u, v in edges) == Counter(range(1, q + 1))
    if target is not None:
        assert f[target] == 0


def check_path(k, p, alpha):
    assert len(p) == 2 * k + 1 and p[k] == alpha
    assert Counter(p) == Counter(range(2 * k + 1))
    assert Counter(abs(a-b) for a, b in zip(p, p[1:])) == Counter(range(1, 2 * k + 1))
    assert all((a <= alpha) != (b <= alpha) for a, b in zip(p, p[1:]))


def main():
    result = {'status': 'PASS', 'center_formula_checks': 0, 'odd_formula_checks': 0,
              'finite_path_certificates': 0, 'full_labelings': 0, 'exact_vertex_zero_checks': 0,
              'negative_controls': 0, 'scope': 'k in {3,5,7,9}; n>=2; m>=0; see proof.md for unbounded argument'}
    for k in range(1, 31):
        for n in range(16):
            for m in (0, 1, 7):
                check(k, n, m, construct.center_zero(k, n, m), 'c')
                result['center_formula_checks'] += 1
    for k in range(3, 202, 2):
        p = construct.near_center_path(k)
        check_path(k, p, k - 1)
        assert p[k-2] == 0 and p[k-1] == 2*k
        result['odd_formula_checks'] += 1
    for cert in construct.CERTS:
        k, p = cert['k'], cert['path']
        check_path(k, p, cert['alpha'])
        assert abs(p.index(0) - k) == cert['zero_depth']
        assert abs(p.index(2*k) - k) == cert['max_depth']
        result['finite_path_certificates'] += 1
    for k in (3, 5, 7, 9):
        for n in (2, 3, 4, 5, 8):
            for m in (0, 1, 2, 5):
                verts, _ = graph(k, n, m)
                for target in verts:
                    f = construct.prescribed_zero(k, n, m, target)
                    check(k, n, m, f, target)
                    result['exact_vertex_zero_checks'] += 1
                for role in ['center', *range(1, k+1)] + (['leaf'] if m else []):
                    f = construct.representative(k, n, m, role)
                    check(k, n, m, f)
                    result['full_labelings'] += 1
    for n, m in ((20, 0), (2, 100), (50, 50)):
        for role in ['center', *range(1, 10)] + (['leaf'] if m else []):
            check(9, n, m, construct.representative(9, n, m, role))
            result['full_labelings'] += 1
    # Deliberate label and alpha-threshold corruption must be detected.
    bad = construct.center_zero(9, 3, 1)
    bad['a', 0, 1] = bad['c']
    try:
        check(9, 3, 1, bad)
    except AssertionError:
        result['negative_controls'] += 1
    else:
        raise AssertionError('label corruption accepted')
    try:
        check_path(9, construct.CERTS[-1]['path'], 7)
    except AssertionError:
        result['negative_controls'] += 1
    else:
        raise AssertionError('wrong alpha accepted')
    Path(__file__).with_name('verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
