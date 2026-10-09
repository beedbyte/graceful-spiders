"""Formula-only growing-depth construction; no solver imports."""
import json
from pathlib import Path

def graceful_permutation(s):
    if type(s) is not int or s<1:raise ValueError('integer s>=1 required')
    p=3*s
    a=[v for j in range(s) for v in (1+3*j,p-3-3*j)]
    a += [2+3*(s-1-i//2 if i%2==0 else i//2) for i in range(s)]
    return a

def offsets(s,r):
    p=3*s
    if type(r) is not int or r<p or r==p+1:raise ValueError('integer r>=3s, r!=3s+1 required')
    x=doubled_core(graceful_permutation(s))
    stop=r if (r-p)%2==0 else r-3
    for b in range(p,stop,2):x.extend((b+1,b+1,b,b))
    if stop==r:x.append(r+1)
    else:x.extend((r-2,r-3,r-3,r-1,r-1,r-2,r+1))
    return x

def path(s,r):
    k=2*r+1
    x=offsets(s,r)
    left=[2*k-v if i%2==0 else v for i,v in enumerate(x)]
    right=[v for j in range(r) for v in (2*r+1+j,2*r-1-j)]+[3*r+2]
    return left[::-1]+[2*r]+right

def spider(s,r,n,m,arm=0,depth=None):
    if depth is None:depth=4*s
    if any(type(v) is not int for v in (n,m,arm,depth)) or n<2 or m<0 or arm not in range(n) or depth not in (4*s,4*s+1):raise ValueError('bad parameters')
    k=2*r+1;a=path(s,r);alpha=2*r;q=(n-2)*k+m
    out={'c':alpha};other=[i for i in range(n) if i!=arm];right=other.pop(0)
    for i,seq in ((arm,a[:k][::-1]),(right,a[k+1:])):
        for d,z in enumerate(seq,1):out[f'a{i}:{d}']=z+(q if z>alpha else 0)
    h=n-2
    for i,arm_id in enumerate(other):
        for d in range(1,k+1):
            out[f'a{arm_id}:{d}']=alpha+((h-i)*k-(d-1)//2 if d%2 else i*k+d//2)
    for j in range(m):out[f'l{j}']=alpha+h*k+j+1
    if depth==4*s+1:out={v:n*k+m-z for v,z in out.items()}
    return out

def doubled_core(a):
    p=len(a)
    y=[v if i%2==0 else p-1-v for i,v in enumerate(a)]
    return y+[p-1-v for v in reversed(y)]

if __name__=='__main__':
    params=[(s,3*s+delta) for s in range(1,26) for delta in (0,2,3,4,5,6)]
    params += [(s,3*s+delta) for s in (50,200,1000) for delta in (0,3)]
    rows={'paths':[{'s':s,'r':r,'path':path(s,r)} for s,r in params],'spiders':[]}
    for s in (1,2,3,8):
        for delta in (0,2,3,6):
            r=3*s+delta
            for n in (2,3,5):
                for m in (0,1,4):
                    for arm in range(n):
                        for depth in (4*s,4*s+1):rows['spiders'].append({'s':s,'r':r,'n':n,'m':m,'arm':arm,'depth':depth,'labels':spider(s,r,n,m,arm,depth)})
    Path(__file__).with_name('certificates.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps({'paths':len(rows['paths']),'spiders':len(rows['spiders'])}))
