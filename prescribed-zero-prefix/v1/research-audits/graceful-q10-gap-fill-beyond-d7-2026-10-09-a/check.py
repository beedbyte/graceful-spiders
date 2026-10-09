"""Private D8 author checker; fresh graph insertion, standard library only."""
from collections import Counter, deque
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
COUNTS = Counter()
GADGETS = {
    9: ([3, 6], [9, 4], [1, 1, 2, 5, 3, 2, 4, 6, 5, 7, 7, 8, 8, 9]),
    10: ([3, 8], [10, 8, 9, 10, 5, 5, 4, 2, 3, 4], [1, 1, 2, 6, 6, 7, 7, 9]),
    11: ([3, 8], [11, 10, 5, 5, 4, 2, 3, 4], [1, 1, 2, 6, 6, 7, 7, 9, 10, 8, 9, 11]),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def tagged(values, side=0):
    return [((side + i) % 2, x) for i, x in enumerate(values)]


def core(path, window=False):
    p = len(path) // 2
    require(len(path) == 2*p, 'even length')
    require(path[0] == (0, 3) and path[-1] == (1, p-4), 'endpoints')
    require([v[0] for v in path] == [i % 2 for i in range(2*p)], 'tags')
    for side in (0, 1):
        require(sorted(x for s, x in path if s == side) == list(range(p)), 'side permutation')
    require(sorted(u[1]+v[1] for u, v in zip(path, path[1:])) == list(range(2*p-1)), 'sum permutation')
    if window:
        z = path.index((1, 0))
        require(path[z-1:z+3] == [(0, 4), (1, 0), (0, 0), (1, 1)], 'compatible window')
        t = next(i for i, v in enumerate(path) if v[1] == p-1)
        require(path[t+1][1] == p-1 and t+1 < z, 'maximum before window')
    COUNTS['core_checks'] += 1


def gadget(q, blocks):
    P, B, D = blocks
    require(all(len(b) > 0 and len(b) % 2 == 0 for b in blocks), 'gadget parity')
    require(P[0] == 3 and B[-1] == 4 and D[0] == 1, 'gadget anchors')
    nodes = tagged(P) + tagged(B, 1) + tagged(D, 1)
    for side in (0, 1):
        require(sorted(x for s, x in nodes if s == side) == list(range(1, q+1)), 'gadget tag partition')
    chains = [P+[q+3], [q+4]+B+[0], [0]+D+[q+1]]
    sums = [u+v for c in chains for u, v in zip(c, c[1:])]
    require(sorted(sums) == list(range(1, 2*q+2))+[2*q+4], 'gadget sum partition')


def insert(path, q):
    core(path, True)
    old_p = len(path)//2
    old_t = next(i for i, v in enumerate(path) if v[1] == old_p-1)
    shifted = [(s, x+q if x else 0) for s, x in path]
    adjacency = {}

    def edge(u, v):
        adjacency.setdefault(u, set()).add(v)
        adjacency.setdefault(v, set()).add(u)

    def chain(nodes):
        for u, v in zip(nodes, nodes[1:]):
            edge(u, v)

    chain(shifted)
    for u, v in [((0, q+4), (1, 0)), ((0, 0), (1, q+1))]:
        adjacency[u].remove(v)
        adjacency[v].remove(u)
    P, B, D = GADGETS[q]
    chain(tagged(P)+[shifted[0]])
    chain([(0, q+4)]+tagged(B, 1)+[(1, 0)])
    chain([(0, 0)]+tagged(D, 1)+[(1, q+1)])
    start, finish = (0, 3), (1, old_p+q-4)
    require({v for v, ns in adjacency.items() if len(ns) == 1} == {start, finish}, 'graph endpoints')
    require(all(len(ns) in (1, 2) for ns in adjacency.values()), 'graph degrees')
    result, previous, current = [], None, start
    while True:
        require(current not in result, 'graph cycle')
        result.append(current)
        remaining = adjacency[current] - ({previous} if previous is not None else set())
        if not remaining:
            break
        require(len(remaining) == 1, 'branch')
        previous, current = current, next(iter(remaining))
    require(len(result) == len(adjacency) and current == finish, 'graph connectivity')
    core(result, True)
    new_t = next(i for i, v in enumerate(result) if v[1] == old_p+q-1)
    require(new_t == old_t+2, 'tracked maximum displacement')
    COUNTS['graph_insertions'] += 1
    return result


def reflected(path):
    p = len(path)//2
    out = tagged([p-1-x for _, x in reversed(path)])
    core(out)
    return out


def f7(p):
    a, r = divmod(p-61, 11)
    return 107+20*a+4*(min(r, 9)//2)


def f8(p):
    a, r = divmod(p-61, 11)
    return 107+20*a+2*r


def construct(row, extra, seeds):
    path = tagged(seeds[row['seed']])
    for q in (9, 10, 11):
        for _ in range(row[f'q{q}']+(extra if q == 11 else 0)):
            path = insert(path, q)
    out = reflected(path)
    require(len(out)//2 == row['p']+11*extra, 'recipe size')
    depths = [i+1 for i, (_, x) in enumerate(out) if x == 0]
    require(depths == [d+20*extra for d in row['depths']], 'recipe depth')
    return out, depths


def spider(path, parity, n, m, selected, depth):
    p = len(path)//2
    k = 2*p+3+parity
    total = n*k+m
    cut = k if parity else k-1
    vals = [2*k-x if s == 0 else x for s, x in path]
    if parity:
        vals += [3*p+5, p+2, 3*p+7, p+3]
        partner = [v for i in range(p) for v in (2*p+5+i, 2*p+3-i)] + [3*p+6, p, 3*p+8, p+1]
    else:
        vals += [3*p+3, p+1, 3*p+4]
        partner = [v for i in range(p) for v in (2*p+3+i, 2*p+1-i)] + [3*p+6, p, 3*p+5]
    h = n-2
    gap = h*k+m
    other = next(a for a in range(n) if a != selected)
    labels = {(-1, 0): cut}
    for arm, series in [(selected, vals), (other, partner)]:
        for t, v in enumerate(series, 1):
            labels[(arm, t)] = v+gap if v > cut else v
    remaining = [a for a in range(n) if a not in (selected, other)]
    for i, arm in enumerate(remaining):
        for t in range(1, k+1):
            labels[(arm, t)] = cut+((h-i)*k-(t-1)//2 if t % 2 else i*k+t//2)
    for j in range(m):
        labels[(n+j, 1)] = cut+h*k+j+1
    require(labels[selected, depth] in (0, total), 'zero or maximum target')
    if labels[selected, depth] == total:
        labels = {v: total-x for v, x in labels.items()}
    # Define the graph from parameters, independently of the label dictionary.
    edges = []
    for arm in range(n):
        for t in range(1, k+1):
            edges.append(((-1, 0) if t == 1 else (arm, t-1), (arm, t)))
    edges += [((-1, 0), (n+j, 1)) for j in range(m)]
    validate_spider(labels, edges, total, (selected, depth), depth)
    COUNTS['actual_spiders'] += 1
    return labels, edges, total


def validate_spider(labels, edges, total, target, depth):
    require(sorted(labels.values()) == list(range(total+1)), 'spider label permutation')
    require(sorted(abs(labels[u]-labels[v]) for u, v in edges) == list(range(1, total+1)), 'spider edge permutation')
    require(labels[target] == 0, 'spider target zero')
    adj = {}
    for u, v in edges:
        adj.setdefault(u, []).append(v)
        adj.setdefault(v, []).append(u)
    dist, queue = {(-1, 0): 0}, deque([(-1, 0)])
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if v not in dist:
                dist[v] = dist[u]+1
                queue.append(v)
    require(len(dist) == total+1 and dist[target] == depth, 'spider BFS')


def reject(name, action, controls):
    try:
        action()
    except (ValueError, KeyError):
        controls.append(name)
    else:
        raise ValueError('negative control accepted: '+name)


def main():
    inputs = json.loads((HERE/'inputs.json').read_text())
    def bindings():
        for rel, digest in inputs.items():
            require(hashlib.sha256((ROOT/rel).read_bytes()).hexdigest() == digest, 'binding: '+rel)
    bindings()
    seed_rows = json.loads((HERE/'seeds.json').read_text())
    seeds = {row['p']: row['core'] for row in seed_rows}
    source_rows = json.loads((ROOT/'research-audits/graceful-beyond-five-sixths-block-principle-2026-10-09-a/data.json').read_text())['seeds'][:2]
    require(seed_rows == source_rows, 'copied seed binding')
    for p, values in seeds.items():
        path = tagged(values)
        core(path, True)
        require(2*p-1-next(i for i, (_, x) in enumerate(path) if x == p-1) == 26, 'seed reflected depth')
    for q, blocks in GADGETS.items():
        gadget(q, blocks)
    recipes = json.loads((HERE/'recipes.json').read_text())
    table = []
    for p in range(61, 72):
        additions = {d for row in recipes if row['p'] == p for d in row['depths']}
        require(set(range(f7(p)+1, f8(p)+1)) <= additions, 'base gap coverage')
        require(f8(p)-f7(p) == [0,2,0,2,0,2,0,2,0,2,4][p-61], 'residue improvement')
        table.append({'p': p, 'k': [2*p+3, 2*p+4], 'F7': f7(p), 'F8': f8(p)})
    for p in range(61, 100001):
        require(f8(p+11) == f8(p)+20 and f7(p+11) == f7(p)+20, 'translation identity')
        require(f8(p) == 2*p-5-2*((p-16+10)//11), 'closed formula')
        require(f8(p) >= f7(p) and f8(p+1) >= f8(p), 'nonregression monotonicity')
    for row in recipes:
        for extra in (0, 1, 2, 7, 19):
            path, depths = construct(row, extra, seeds)
            for parity in (0, 1):
                for n, m in ((2,0), (3,0), (3,2), (5,7)):
                    for selected in (0, n-1):
                        for depth in depths:
                            spider(path, parity, n, m, selected, depth)
    defects = [10*(2*p+3+e)-11*f8(p) for p in range(61,72) for e in (0,1)]
    require(min(defects) == 53 and max(defects) == 83, 'tail deficit bounds')
    controls = []
    for q in (9,10,11):
        broken = [list(x) for x in GADGETS[q]]
        broken[0][1] += 1
        reject(f'q{q} corrupt prefix', lambda q=q, broken=broken: gadget(q, broken), controls)
    bad = dict(recipes[0], p=63)
    reject('wrong recipe size', lambda: construct(bad, 0, seeds), controls)
    bad_depth = dict(recipes[0], depths=[106,107])
    reject('wrong reflected gain', lambda: construct(bad_depth, 0, seeds), controls)
    reject('premature reflection', lambda: insert(reflected(tagged(seeds[16])),10), controls)
    reject('r10 single pair misses first gap', lambda: require(set(range(124,128)) <= {126,127}, 'missing 124/125'), controls)
    path, depths = construct(recipes[0], 0, seeds)
    for parity in (0,1):
        labels, edges, total = spider(path, parity, 3, 2, 2, depths[0])
        broken = dict(labels)
        broken[2, depths[0]] = broken[-1,0]
        reject(f'parity{parity} duplicated zero target', lambda: validate_spider(broken,edges,total,(2,depths[0]),depths[0]), controls)
        reject(f'parity{parity} wrong depth', lambda: validate_spider(labels,edges,total,(2,depths[0]),depths[0]+1), controls)
        partial = dict(labels)
        for t in range(1, (total-2)//3+1):
            partial[2,t] = total-partial[2,t]
        reject(f'parity{parity} partial complement', lambda: validate_spider(partial,edges,total,(2,depths[1]),depths[1]), controls)
    bindings()
    print(json.dumps({'status':'PASS; author candidate awaiting separate audit', 'table':table, 'counts':dict(COUNTS), 'negative_controls':controls, 'diagnostic_p':[61,100000], 'tail_deficit':[min(defects),max(defects)], 'proof_scope':'D8 extension at all p>=61, both k parities and all n>=2,m>=0; slope unchanged at 10/11'}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
