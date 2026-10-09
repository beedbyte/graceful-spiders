"""Private arithmetic/core/spider certificate; standard library; read-only replay."""
import collections
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
B = [26, 26, 26, 26, 24, 27]
C6 = [3,3,2,1,1,0,0,4,4,5,5,2]
G = {
    '11': (11,[3,8],[11,10,5,5,4,2,3,4],[1,1,2,6,6,7,7,9,10,8,9,11]),
    '9fast': (9,[3,6],[9,4],[1,1,2,5,3,2,4,6,5,7,7,8,8,9]),
    '9slow': (9,[3,5,6,6],[9,4],[1,1,2,5,4,2,3,7,7,8,8,9]),
}
COUNT = collections.Counter()

def need(ok, msg):
    if not ok:
        raise ValueError(msg)

def old(p):
    return 11 if p < 16 else 27 if p < 25 else 25+16*((p-16)//9)

def f(p):
    a,r = divmod(p-61,11)
    return 107+20*a+4*(min(r,9)//2)

def d7(k):
    p=(k-3)//2
    return old(p) if k<125 else f(p)

def k7(d):
    if d<=11:return 19
    if d<=27:return 35
    if d<=89:return 35+18*((d-25+15)//16)
    a=max(0,(d-123+19)//20)
    s=max(0,(d-107-20*a+3)//4)
    return 125+22*a+4*s

def intervals(p):
    for a in range((p-16)//11+1):
        for j in range((p-16-11*a)//9+1):
            r,de=divmod(p-16-11*a-9*j,6)
            yield dict(p=p,a=a,j=j,delta=de,padding=r,
                       lo=B[de]+20*a+14*j,hi=B[de]+20*a+16*j+1)

def chain(p, start, finish):
    d=start
    out=[]
    for row in sorted(intervals(p),key=lambda x:(x['lo'],x['hi'])):
        if row['lo']<=d+1 and row['hi']>d:
            out.append(row)
            d=row['hi']
        if d>=finish:
            return out
    raise ValueError(('uncovered',p,d,finish))

def core(c, compatible=False):
    p=len(c)//2
    need(len(c)==2*p and c[0]==3 and c[-1]==p-4,'core endpoints')
    need(sorted(c[::2])==list(range(p)) and sorted(c[1::2])==list(range(p)),'sides')
    need(sorted(x+y for x,y in zip(c,c[1:]))==list(range(2*p-1)),'sums')
    if compatible:
        z=c.index(0)
        need(z%2==1 and c[z-1:z+3]==[4,0,0,1],'window')
        t=c.index(p-1)
        need(c[t:t+2]==[p-1,p-1] and t+1<z,'tracked maximum')
    COUNT['core_checks']+=1

def insert(c,name):
    q,P,bb,dd=G[name]
    z=c.index(0)
    out=P+[v+q for v in c[:z]]+bb+[0,0]+dd+[v+q for v in c[z+2:]]
    core(out,True)
    return out

def build(row,s,seeds):
    c=list(seeds[row['delta']]['core'])
    for _ in range(row['a']): c=insert(c,'11')
    for _ in range(s): c=insert(c,'9fast')
    for _ in range(row['j']-s): c=insert(c,'9slow')
    x=len(c)//2
    c=[x-1-v for v in c[::-1]]
    core(c)
    for _ in range(row['padding']):
        x=len(c)//2
        c += [x+v for v in C6]
        core(c)
    need(len(c)==2*row['p'],'target size')
    depths=[i+1 for i,v in enumerate(c) if v==0]
    first=row['lo']+2*s
    need(depths==[first,first+1],'tracked depths')
    return c,depths

def spider(c,even,n,m,selected,depth):
    p=len(c)//2
    k=2*p+3+even
    M=2*k
    A=2*p+2 if not even else 2*p+4
    arm=[M-v if i%2==0 else v for i,v in enumerate(c)]
    if not even:
        arm += [3*p+3,p+1,3*p+4]
        partner=[v for i in range(p) for v in (2*p+3+i,2*p+1-i)]
        partner += [3*p+6,p,3*p+5]
    else:
        arm += [3*p+5,p+2,3*p+7,p+3]
        partner=[v for i in range(p) for v in (2*p+5+i,2*p+3-i)]
        partner += [3*p+6,p,3*p+8,p+1]
    other=next(i for i in range(n) if i!=selected)
    h=n-2
    Q=h*k+m
    labels={(-1,0):A}
    for ai,vals in [(selected,arm),(other,partner)]:
        for t,v in enumerate(vals,1):labels[ai,t]=v+Q if v>A else v
    residual=[i for i in range(n) if i not in (selected,other)]
    for i,ai in enumerate(residual):
        for t in range(1,k+1):
            v=(h-i)*k-(t-1)//2 if t%2 else i*k+t//2
            labels[ai,t]=v+A
    for i in range(m):labels[n+i,1]=h*k+i+1+A
    N=n*k+m
    if labels[selected,depth]==N:labels={v:N-x for v,x in labels.items()}
    need(labels[selected,depth]==0,'actual requested zero')
    need(sorted(labels.values())==list(range(N+1)),'actual labels')
    adj=collections.defaultdict(list)
    weights=[]
    for v in labels:
        if v==(-1,0):continue
        ai,t=v
        parent=(-1,0) if t==1 else (ai,t-1)
        adj[v].append(parent);adj[parent].append(v)
        weights.append(abs(labels[v]-labels[parent]))
    need(sorted(weights)==list(range(1,N+1)),'actual edge weights')
    dist={(-1,0):0};queue=collections.deque(dist)
    while queue:
        v=queue.popleft()
        for w in adj[v]:
            if w not in dist:dist[w]=dist[v]+1;queue.append(w)
    need(len(dist)==N+1 and dist[selected,depth]==depth,'actual BFS depth')
    COUNT['actual_spiders']+=1

def main():
    bindings=json.loads((HERE/'inputs.json').read_text())
    for rel,digest in bindings.items():
        need(hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==digest,'input hash '+rel)
    seeds=json.loads((ROOT/'research-audits/graceful-beyond-five-sixths-block-principle-2026-10-09-a/data.json').read_text())['seeds']
    for de,row in enumerate(seeds):
        c=row['core'];core(c,True)
        need(row['p']==16+de and 2*row['p']-1-c.index(row['p']-1)==B[de],'seed depth')
    for q,P,bb,dd in G.values():
        need(all(len(v)%2==0 and v for v in (P,bb,dd)),'block parity')
        need(P[0]==3 and bb[-1]==4 and dd[0]==1,'gadget interface')
        need(sorted(P[::2]+bb[1::2]+dd[1::2])==list(range(1,q+1)),'gadget H')
        need(sorted(P[1::2]+bb[::2]+dd[::2])==list(range(1,q+1)),'gadget L')
        chains=[P+[q+3],[q+4]+bb+[0],[0]+dd+[q+1]]
        sums=[x+y for c in chains for x,y in zip(c,c[1:])]
        need(sorted(sums)==list(range(1,2*q+2))+[2*q+4],'gadget sums')
    bases={str(p):chain(p,old(p),f(p)) for p in range(61,67)}
    bridges={str(p):chain(p,f(p-6),f(p)) for p in range(67,78)}
    # Finite arithmetic certificates used by the unbounded induction proof.
    for p in range(61,160):need(f(p)>=old(p),'nonregression residue99')
    need(all(f(p+99)==f(p)+180 and old(p+99)==old(p)+176 for p in range(61,160)),'period99')
    for p in range(61,72):
        candidates=[]
        for de in range(6):
            for j in range(12):
                if (p-16-de-9*j)%11:continue
                a=(p-16-de-9*j)//11
                # a may be negative: endpoint algebra remains valid and is an upper bound.
                lo=B[de]+20*a+14*j;hi=lo+2*j+1
                candidates.append((lo,hi))
        above=[(lo,hi) for lo,hi in candidates if hi>f(p)]
        need(above==([(f(p)+3,f(p)+4)] if p%11==5 else []),'exact top obstruction')
    recipes=[r for group in (bases,bridges) for rows in group.values() for r in rows]
    # All arithmetic choices in finite induction recipes are realized as cores,
    # plus translations by 1 and 7 q11 steps; then checked on actual spiders.
    for row in recipes:
        for extra in (0,1,7):
            row=dict(row,p=row['p']+11*extra,a=row['a']+extra,
                     lo=row['lo']+20*extra,hi=row['hi']+20*extra)
            for s in range(row['j']+1):
                c,depths=build(row,s,seeds)
                for even in (0,1):
                    for n,m in ((2,0),(3,2),(5,0)):
                        for selected in sorted({0,n-1}):
                            for depth in depths:spider(c,even,n,m,selected,depth)
    for de in range(6):
        row=next(r for r in recipes if r['delta']==de)
        row=dict(row,p=row['p']+12,padding=row['padding']+2)
        for s in sorted({0,row['j']}):
            c,depths=build(row,s,seeds)
            for even in (0,1):
                for depth in depths:spider(c,even,3,0,2,depth)
    maxdef=max(10*k-11*d7(k) for k in range(19,125))
    need(maxdef==261,'early deficit')
    tail=[10*(2*p+3+e)-11*f(p) for p in range(61,72) for e in (0,1)]
    need(min(tail)==57 and max(tail)==107,'tail deficit')
    for d in range(2,10001):
        k=k7(d)
        need(d7(k)>=d and (k==19 or d7(k-1)<d),'inverse threshold')
    # Diagnostic cross-check only: theorem uses finite base/bridge certificates.
    for p in range(61,501):
        top=old(p)
        for row in sorted(intervals(p),key=lambda x:(x['lo'],x['hi'])):
            if row['lo']<=top+1:top=max(top,row['hi'])
        need(top==f(p),'direct exact union')
    out=dict(status='PASS; q11 separate internal acceptance bound in inputs.json',
             bases=bases,bridges=bridges,counts=dict(COUNT),
             exact_union_diagnostic_p=[61,500],global_deficit_bound=261,
             tail_deficit=[57,107],negative_controls=0)
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__':main()
