"""Independent dense-array verifier and construction, standard library only.

Run: python -B verify_independent.py
Writes only this directory; never runs or imports the supplied verifier/search.
The supplied construct module is checked separately as a witness producer.
"""
import sys
sys.dont_write_bytecode = True
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent
CERTS = json.loads((SOURCE / 'certificates.json').read_text())['certificates']


def require(condition, message):
    if not condition:
        raise ValueError(message)


def edges(k, n, m):
    for arm in range(n):
        chain = [0] + list(range(1 + arm*k, 1 + (arm+1)*k))
        yield from zip(chain, chain[1:])
    yield from ((0, j) for j in range(n*k+1, n*k+m+1))


def check(k, n, m, labels, target=None):
    q = n*k+m
    require(len(labels) == q+1, 'vertex count')
    require(all(type(x) is int for x in labels), 'integer labels')
    require(sorted(labels) == list(range(q+1)), 'vertex permutation')
    differences = [abs(labels[u]-labels[v]) for u, v in edges(k,n,m)]
    require(sorted(differences) == list(range(1,q+1)), 'edge permutation')
    if target is not None:
        require(labels[target] == 0, 'prescribed zero')


def center(k, n, m):
    # Populate even and odd levels separately, in dense vertex order.
    labels = [0] * (n*k+m+1)
    for arm in range(n):
        for depth in range(2,k+1,2):
            labels[arm*k+depth] = arm*k+depth//2
        for depth in range(1,k+1,2):
            labels[arm*k+depth] = (n-arm)*k-(depth-1)//2
    labels[n*k+1:] = range(n*k+1,n*k+m+1)
    return labels


def uniform_path(k):
    r=(k-1)//2
    left=[None]*k
    right=[None]*k
    for j in range(r+1):
        left[2*j]=4*r+2-j
        right[2*j]=2*r+1+j
    for j in range(1,r+1):
        left[2*j-1]=j-1
        right[2*j-1]=2*r-j
    return left[::-1]+[2*r]+right


def path_check(k, path, threshold):
    require(len(path)==2*k+1, 'path length')
    require(sorted(path)==list(range(2*k+1)), 'path labels')
    require(sorted(abs(u-v) for u,v in zip(path,path[1:]))==list(range(1,2*k+1)), 'path differences')
    require(path[k]==threshold, 'midpoint equals alpha')
    require(all((u<=threshold)!=(v<=threshold) for u,v in zip(path,path[1:])), 'alpha crossing')


def own_witness(k,n,m,role):
    q=n*k+m
    if role==0:
        return center(k,n,m)
    if role=='short':
        old=center(k,n,m-1)
        return [q-x for x in old]+[0]
    if role in (k-1,k):
        base=center(k,n-1,m)
        arms=base[1:(n-1)*k+1]
        leaves=base[(n-1)*k+1:]
        labels=[0]+arms+leaves
        new_arm=[]
        for _ in range(k):
            new_max=len(labels)+len(new_arm)
            labels=[new_max-x for x in labels]
            new_arm=[new_max-x for x in new_arm]+[0]
        labels=labels[:(n-1)*k+1]+new_arm+labels[(n-1)*k+1:]
        return [q-x for x in labels] if role==k-1 else labels
    paths=[uniform_path(k)]+[c['path'] for c in CERTS if c['k']==k]
    path=next(p for p in paths if role in (abs(p.index(0)-k),abs(p.index(2*k)-k)))
    alpha=path[k]
    rest=center(k,n-2,m)
    shift=q-2*k
    expanded=[x if x<=alpha else x+shift for x in path]
    labels=[alpha]+expanded[:k][::-1]+expanded[k+1:]+[x+alpha for x in rest[1:]]
    if abs(path.index(0)-k)!=role:
        labels=[q-x for x in labels]
    return labels


def exact_own(k,n,m,target):
    role=0 if target==0 else ((target-1)%k+1 if target<=n*k else 'short')
    labels=own_witness(k,n,m,role)
    old=labels.index(0)
    if target>n*k:
        labels[target],labels[old]=labels[old],labels[target]
    elif target:
        old_arm=(old-1)//k
        new_arm=(target-1)//k
        for depth in range(1,k+1):
            u,v=old_arm*k+depth,new_arm*k+depth
            labels[u],labels[v]=labels[v],labels[u]
    return labels


def external_as_dense(module,k,n,m,target):
    names=['c']+[('a',a,d) for a in range(n) for d in range(1,k+1)]+[('p',i) for i in range(m)]
    result=module.prescribed_zero(k,n,m,names[target])
    require(set(result)==set(names),'external vertex identities')
    return [result[v] for v in names]


def main():
    report={'status':'PASS','center_checks':0,'uniform_path_checks':0,'finite_certificates':0,
            'independent_exact_vertex_checks':0,'supplied_exact_vertex_checks':0,'stress_checks':0,
            'negative_controls':0,'even_obstruction_permutation_checks':{}}
    spec=importlib.util.spec_from_file_location('audited_construct',SOURCE/'construct.py')
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    for k in range(1,65):
        for n in range(21):
            for m in (0,1,7,50):
                check(k,n,m,center(k,n,m),0)
                report['center_checks']+=1
    for k in range(3,402,2):
        p=uniform_path(k)
        path_check(k,p,k-1)
        require(p[k-2]==0 and p[k-1]==2*k,'uniform extremes')
        report['uniform_path_checks']+=1
    for cert in CERTS:
        k,p=cert['k'],cert['path']
        path_check(k,p,cert['alpha'])
        require(abs(p.index(0)-k)==cert['zero_depth'],'certificate zero depth')
        require(abs(p.index(2*k)-k)==cert['max_depth'],'certificate maximum depth')
        report['finite_certificates']+=1
    for k in (3,5,7,9):
        for n in range(2,13):
            for m in range(8):
                for target in range(n*k+m+1):
                    check(k,n,m,exact_own(k,n,m,target),target)
                    report['independent_exact_vertex_checks']+=1
                    check(k,n,m,external_as_dense(module,k,n,m,target),target)
                    report['supplied_exact_vertex_checks']+=1
    for k in (3,5,7,9):
        for n,m in ((2,10000),(1000,0),(100,100)):
            for target in [0,*range(1,k+1),n*k]+([n*k+m] if m else []):
                check(k,n,m,exact_own(k,n,m,target),target)
                check(k,n,m,external_as_dense(module,k,n,m,target),target)
                report['stress_checks']+=2
    # An independent exhaustive finite check of the separate even-k obstruction.
    # Fix midpoint k and its right neighbor 2k; reflection covers the other side.
    for k in (2,4):
        positions=[j for j in range(2*k+1) if j not in (k,k+1)]
        remaining=[j for j in range(2*k+1) if j not in (k,2*k)]
        checked=0
        for permutation in itertools.permutations(remaining):
            p=[None]*(2*k+1)
            p[k],p[k+1]=k,2*k
            for j,x in zip(positions,permutation):
                p[j]=x
            require(sorted(abs(u-v) for u,v in zip(p,p[1:]))!=list(range(1,2*k+1)), 'even obstruction counterexample')
            checked+=1
        report['even_obstruction_permutation_checks'][str(k)]=checked
    checks=[lambda: check(3,2,0,[0]*7),lambda: check(3,2,0,center(3,2,0),1),
            lambda: path_check(9,CERTS[-1]['path'],7)]
    for bad in checks:
        try:
            bad()
        except ValueError:
            report['negative_controls']+=1
        else:
            raise ValueError('negative control accepted')
    report['source_sha256']={name:hashlib.sha256((SOURCE/name).read_bytes()).hexdigest()
                            for name in ('proof.md','construct.py','verify.py','certificates.json','literature.md')}
    report['limits']='Finite tests check implementations; universal claims rest on the separately audited argument. No formal proof assistant or external peer review.'
    (HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
