"""Separate construction and verifier. No imports from the audited packages."""
import hashlib
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent
C = ('center',)
K = 11

def require(condition, message):
    if not condition:
        raise ValueError(message)

def graph(arms, leaves):
    edges = []
    for arm in arms:
        previous = C
        for depth in range(1, K+1):
            vertex = ('arm', arm, depth)
            edges.append((previous, vertex))
            previous = vertex
    edges += [(C, ('leaf', leaf)) for leaf in leaves]
    return {C} | {v for edge in edges for v in edge}, edges

def verify(labels, arms, leaves, target):
    vertices, edges = graph(arms, leaves)
    require(set(labels) == vertices, 'Wrong vertex domain')
    require(Counter(labels.values()) == Counter(range(len(edges)+1)), 'Wrong labels')
    require(Counter(abs(labels[u]-labels[v]) for u,v in edges)
            == Counter(range(1, len(edges)+1)), 'Wrong edge differences')
    require(labels[target] == 0, 'Wrong zero vertex')

def centered(arms, leaves):
    arms, leaves = list(arms), list(leaves)
    f = {C: 0}
    # Partition each block among even depths of one arm and odd depths
    # of the opposite arm. This builds the center formula by label blocks.
    for block in range(len(arms)):
        for offset in range(1, 6):
            f['arm', arms[block], 2*offset] = K*block + offset
        for offset in range(6):
            f['arm', arms[-1-block], 2*offset+1] = K*(block+1)-offset
    for index, leaf in enumerate(leaves, 1):
        f['leaf', leaf] = K*len(arms)+index
    return f

def alpha_check(path, expected_zero, expected_max):
    require(Counter(path) == Counter(range(23)), 'Path label multiset')
    require(path[11] == 10, 'Midpoint is not threshold')
    differences = [abs(path[i]-path[i+1]) for i in range(22)]
    require(Counter(differences) == Counter(range(1,23)), 'Path differences')
    require(all((path[i]<=10) != (path[i+1]<=10) for i in range(22)), 'Alpha crossing')
    require(abs(path.index(0)-11) == expected_zero, 'Wrong zero depth')
    require(abs(path.index(22)-11) == expected_max, 'Wrong maximum depth')
    return differences

def compose(path, n, m, target_arm, extreme):
    # Put the side containing the requested extremum directly on target_arm.
    target_side = -1 if path.index(extreme)<11 else 1
    other_arm = next(arm for arm in range(n) if arm != target_arm)
    rest = [arm for arm in range(n) if arm not in (target_arm, other_arm)]
    qrest = K*len(rest)+m
    f = {v:x+10 for v,x in centered(rest, range(m)).items()}
    for arm, side in ((target_arm,target_side), (other_arm,-target_side)):
        for depth in range(1,12):
            value = path[11+side*depth]
            f['arm',arm,depth] = value + (qrest if value>10 else 0)
    if extreme == 22:
        f = {v:K*n+m-x for v,x in f.items()}
    return f

def grow_zero(f, vertex):
    # A tree on len(f) vertices receives its next maximum label.
    maximum = len(f)
    f[vertex] = maximum
    return {v:maximum-x for v,x in f.items()}

def endpoint(n, m, arm, depth):
    f = centered([a for a in range(n) if a != arm], range(m))
    for d in range(1,12):
        f = grow_zero(f, ('arm',arm,d))
    if depth == 10:
        f = {v:K*n+m-x for v,x in f.items()}
    return f

def uniform_path():
    left = [22-j if d%2 else j-1 for d in range(1,12) for j in [(d-1)//2 if d%2 else d//2]]
    right = [11+(d-1)//2 if d%2 else 10-d//2 for d in range(1,12)]
    return left[::-1]+[10]+right

def main():
    data = json.loads((SOURCE/'certificates.json').read_text())
    require(data['k']==11 and data['alpha']==10, 'Wrong global metadata')
    certs = data['certificates']
    require(len(certs)==4, 'Wrong certificate count')
    summaries=[]
    coverage=set()
    for cert in certs:
        require(cert['status']=='FOUND', 'Wrong status')
        d0,dq=cert['zero_depth'],cert['max_depth']
        ds=alpha_check(cert['path'],d0,dq)
        coverage.update((d0,dq))
        summaries.append({'zero_depth':d0,'max_depth':dq,'differences':ds})
    require(coverage == set(range(2,10)), 'Missing intermediate depth')
    standard=uniform_path()
    alpha_check(standard,2,1)
    counts=Counter()
    for h in range(21):
        for m in (0,1,7,30):
            verify(centered(range(h),range(m)),range(h),range(m),C)
            counts['centered']+=1
    # Every vertex for every graph in this grid: no metadata-only coverage.
    for n in range(2,13):
        for m in range(8):
            verify(centered(range(n),range(m)),range(n),range(m),C)
            counts['all_vertices']+=1
            for leaf in range(m):
                f=centered(range(n),[j for j in range(m) if j!=leaf])
                f=grow_zero(f,('leaf',leaf))
                verify(f,range(n),range(m),('leaf',leaf))
                counts['all_vertices']+=1
            for arm in range(n):
                for depth in range(1,12):
                    if depth in (10,11):
                        f=endpoint(n,m,arm,depth)
                    elif depth==1:
                        f=compose(standard,n,m,arm,22)
                    else:
                        cert=next(c for c in certs if depth in (c['zero_depth'],c['max_depth']))
                        extreme=0 if depth==cert['zero_depth'] else 22
                        f=compose(cert['path'],n,m,arm,extreme)
                    verify(f,range(n),range(m),('arm',arm,depth))
                    counts['all_vertices']+=1
    for n,m in ((2,10000),(1000,0),(100,100)):
        for cert in certs:
            for extreme,key in ((0,'zero_depth'),(22,'max_depth')):
                for arm in (0,n-1):
                    verify(compose(cert['path'],n,m,arm,extreme),range(n),range(m),('arm',arm,cert[key]))
                    counts['stress_compositions']+=1
    bad=certs[0]['path'].copy()
    bad[0]=bad[1]
    for path,d0,dq in ((bad,2,3),(certs[0]['path'],4,3),(certs[0]['path'],2,5)):
        try:
            alpha_check(path,d0,dq)
        except ValueError:
            counts['negative_cases']+=1
        else:
            raise ValueError('Bad certificate accepted')
    paths=[SOURCE/name for name in ('proof.md','certificates.json','check.py','search.js')]
    paths += [HERE.parent.parent/'proof.md', HERE/'AUDIT.md']
    result={'status':'PASS','counts':dict(counts),'certificates':summaries,
            'all_vertex_grid':{'n':'2..12','m':'0..7','k':11},
            'boundary_n2_m0':'all 23 vertices checked',
            'sha256':{p.relative_to(HERE.parent.parent).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
            'limits':'Finite tests support transcription; all-parameter proof is assessed in AUDIT.md. Search counts not reproduced. No novelty or external-peer-review claim.'}
    (HERE/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
