"""Independent exact certificate verifier; imports no search or earlier checker.

The mathematical all-parameter claim uses the interval proof in proof.md;
the finite composition checks here catch transcription/implementation errors.
"""
import json
from pathlib import Path


def check_path(path, zero_depth, max_depth):
    assert len(path) == 23 and sorted(path) == list(range(23))
    assert path[11] == 10
    differences = [abs(x-y) for x, y in zip(path, path[1:])]
    assert sorted(differences) == list(range(1, 23))
    assert all((x <= 10) != (y <= 10) for x, y in zip(path, path[1:]))
    assert abs(path.index(0)-11) == zero_depth
    assert abs(path.index(22)-11) == max_depth
    return differences


def compose(path, n, m):
    # Vertices: center=0; arms in consecutive blocks of 11; then leaves.
    q = 11*n+m
    extra = 11*(n-2)+m
    labels = [None]*(q+1)
    labels[0] = 10
    for arm in range(2):
        for depth in range(1, 12):
            x = path[11-depth if arm == 0 else 11+depth]
            labels[1+arm*11+depth-1] = x + (extra if x > 10 else 0)
    for arm in range(n-2):
        for depth in range(1, 12):
            x = ((n-2-arm)*11-(depth-1)//2 if depth % 2
                 else arm*11+depth//2)
            labels[1+(arm+2)*11+depth-1] = x+10
    for leaf in range(m):
        labels[1+11*n+leaf] = 10+11*(n-2)+leaf+1
    return labels


def check_spider(labels, n, m, zero_arm, zero_depth):
    q = 11*n+m
    assert sorted(labels) == list(range(q+1))
    differences = []
    for arm in range(n):
        vertices = [0]+list(range(1+arm*11, 1+(arm+1)*11))
        differences += [abs(labels[u]-labels[v]) for u,v in zip(vertices,vertices[1:])]
    differences += [abs(labels[0]-labels[v]) for v in range(1+11*n, q+1)]
    assert sorted(differences) == list(range(1,q+1))
    assert labels[1+zero_arm*11+zero_depth-1] == 0


def main():
    data = json.loads(Path(__file__).with_name('certificates.json').read_text())
    coverage = {1,2,10,11}  # Existing general formula and reversible leaf operation.
    checks = 0
    for certificate in data['certificates']:
        path = certificate['path']
        d0, dq = certificate['zero_depth'], certificate['max_depth']
        ds = check_path(path,d0,dq)
        coverage.update((d0,dq))
        print(f"FOUND: zero depth {d0}, maximum depth {dq}; differences {ds}")
        for n in (2,3,4,5,8,20):
            for m in (0,1,2,5,30):
                f = compose(path,n,m)
                for depth, extreme in ((d0,0),(dq,22)):
                    old_arm = 0 if path.index(extreme) < 11 else 1
                    g = f if extreme == 0 else [11*n+m-x for x in f]
                    # Verify zero at every exact arm by swapping whole arm blocks.
                    for arm in range(n):
                        moved = g.copy()
                        for j in range(11):
                            u,v = 1+old_arm*11+j,1+arm*11+j
                            moved[u],moved[v] = moved[v],moved[u]
                        check_spider(moved,n,m,arm,depth)
                        checks += 1
    assert coverage == set(range(1,12))
    # Exercise negative checks, both labels and advertised target metadata.
    corrupt = data['certificates'][0]['path'].copy()
    corrupt[0] = corrupt[1]
    for path,d0,dq in ((corrupt,2,3),(data['certificates'][0]['path'],4,3)):
        try:
            check_path(path,d0,dq)
        except AssertionError:
            pass
        else:
            raise AssertionError('Corrupt certificate accepted')
    print(f"PASS: 4 exact alpha paths; {checks} prescribed-vertex composition checks; "
          "2 corrupt inputs rejected; depth coverage 1..11.")


if __name__ == '__main__':
    main()
