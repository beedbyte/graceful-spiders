"""Standard-library certificate checker; imports no constructor or solver."""
import json,itertools
from pathlib import Path

def check_path(s,r,a):
    k=2*r+1;alpha=k-1
    assert len(a)==2*k+1
    assert sorted(a)==list(range(2*k+1))
    assert a[k]==alpha
    assert all((u<=alpha)!=(v<=alpha) for u,v in zip(a,a[1:]))
    assert sorted(abs(u-v) for u,v in zip(a,a[1:]))==list(range(1,2*k+1))
    assert a[k-4*s]==0 and a[k-(4*s+1)]==2*k
    assert a[0]==3*r+1 and a[-1]==3*r+2

def check_spider(s,r,n,m,arm,depth,a):
    k=2*r+1;q=n*k+m
    vertices={'c'}|{f'a{i}:{d}' for i in range(n) for d in range(1,k+1)}|{f'l{j}' for j in range(m)}
    assert set(a)==vertices
    assert sorted(a.values())==list(range(q+1))
    edges=[]
    for i in range(n):
        prev='c'
        for d in range(1,k+1):
            cur=f'a{i}:{d}';edges.append((prev,cur));prev=cur
    edges += [('c',f'l{j}') for j in range(m)]
    assert sorted(abs(a[u]-a[v]) for u,v in edges)==list(range(1,q+1))
    assert a[f'a{arm}:{depth}']==0

def check_core():
    a=[1,3,4,0,5,2];p=6
    assert sorted(a)==list(range(p))
    assert sorted(abs(u-v) for u,v in zip(a,a[1:]))==list(range(1,p))
    y=[v if i%2==0 else p-1-v for i,v in enumerate(a)]
    core=y+[p-1-v for v in y[::-1]]
    assert core==[1,2,4,5,5,3,2,0,0,1,3,4]
    assert sorted(core[::2])==list(range(p)) and sorted(core[1::2])==list(range(p))
    assert sorted(u+v for u,v in zip(core,core[1:]))==list(range(2*p-1))

def check_formula(s,r):
    # Reconstruct by residues and symmetry, without importing the author program.
    p=3*s
    first=[]
    for low_up,low_down in zip(range(1,p,3),range(p-3,-1,-3)):
        first += [low_up,low_down]
    residue=list(range(2,p,3));tail=[]
    while residue:
        tail.append(residue.pop())
        if residue:tail.append(residue.pop(0))
    a=first+tail
    assert sorted(a)==list(range(p))
    assert sorted(abs(u-v) for u,v in zip(a,a[1:]))==list(range(1,p))
    assert a[0]==1 and a[2*s-1]==0 and a[2*s]==p-1
    core=[v if i%2==0 else p-1-v for i,v in enumerate(a)]
    core += [p-1-v for v in core[::-1]]
    assert sorted(core[::2])==list(range(p)) and sorted(core[1::2])==list(range(p))
    assert sorted(u+v for u,v in zip(core,core[1:]))==list(range(2*p-1))
    target=r if (r-p)%2==0 else r-3
    cur=p
    while cur<target:
        core += [cur+1,cur+1,cur,cur];cur+=2
    if target==r:core.append(r+1)
    else:core += [r-2,r-3,r-3,r-1,r-1,r-2,r+1]
    assert len(core)==2*r+1
    assert sorted(core[::2])==list(range(r))+[r+1]
    assert sorted(core[1::2])==list(range(r))
    assert sorted(u+v for u,v in zip(core,core[1:]))==list(range(2*r))
    return core

def main():
    data=json.loads(Path(__file__).with_name('certificates.json').read_text())
    for row in data['paths']:
        check_path(row['s'],row['r'],row['path'])
        core=check_formula(row['s'],row['r']);k=2*row['r']+1
        left=row['path'][:k][::-1]
        assert core==[2*k-v if i%2==0 else v for i,v in enumerate(left)]
    for row in data['spiders']:
        check_spider(row['s'],row['r'],row['n'],row['m'],row['arm'],row['depth'],row['labels'])
    check_core()
    bad=data['paths'][0]['path'].copy();bad[0]=bad[1]
    try:check_path(1,3,bad)
    except AssertionError:pass
    else:raise RuntimeError('corrupt vertices accepted')
    bad=data['paths'][0]['path'].copy();bad[0],bad[2]=bad[2],bad[0]
    try:check_path(1,3,bad)
    except AssertionError:pass
    else:raise RuntimeError('corrupt edges accepted')
    result={'verdict':'PASS','paths':len(data['paths']),'spiders':len(data['spiders']),'corruptions_rejected':2,'independent_agent_audit':False}
    Path(__file__).with_name('verification-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__=='__main__':main()
