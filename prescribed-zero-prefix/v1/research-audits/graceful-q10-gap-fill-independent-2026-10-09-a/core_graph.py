"""Separate standard-library reconstruction. No author Python is imported."""
import json, hashlib, itertools
from pathlib import Path
from collections import defaultdict, deque

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'graceful-compatible-seed-prefix-2026-10-09-a'
C6 = [3,3,2,1,1,0,0,4,4,5,5,2]
PICKS = {16:16,17:22,18:22,19:20,20:24,21:22}
COUNTS = defaultdict(int)

def need(ok, why):
    if not ok: raise ValueError(why)

def load(name):
    return json.loads((BASE/name).read_text(encoding='utf-8-sig'))

SEEDS = {(r['p'],r['d']):r['core'] for r in load('seeds.json')}
SMALL = {(r['p'],r['zero_depth']):r['path'] for r in load('small-seeds.json')}
GADGETS = load('old-data.json')['gadgets']
G18 = load('gadget30.json')

def core(c, compatible=False):
    p = len(c)//2
    need(len(c)==2*p and p>=4, 'core size')
    need(c[0]==3 and c[-1]==p-4, 'endpoints')
    need(sorted(c[::2])==list(range(p)), 'H permutation')
    need(sorted(c[1::2])==list(range(p)), 'L permutation')
    need(sorted(a+b for a,b in zip(c,c[1:]))==list(range(2*p-1)), 'sum permutation')
    if compatible:
        z=next(i for i in range(1,len(c),2) if c[i]==0)
        need(c[z-1:z+3]==[4,0,0,1], 'compatible window')
    COUNTS['core_checks']+=1
    return p

def tagged(c):
    return [(i%2,x) for i,x in enumerate(c)]

def extend(c,g,q):
    p=core(c,True)
    old=tagged(c)
    old=[(t,v+q if v else 0) for t,v in old]
    adj=defaultdict(set)
    def add(a,b):
        need(a!=b and b not in adj[a], 'duplicate edge')
        adj[a].add(b);adj[b].add(a)
    def chain(v):
        for a,b in zip(v,v[1:]):add(a,b)
    chain(old)
    for a,b in [((0,q+4),(1,0)),((0,0),(1,q+1))]:
        need(b in adj[a], 'missing cut')
        adj[a].remove(b);adj[b].remove(a)
    P=tagged(g['P'])
    B=[(1-i%2,v) for i,v in enumerate(g['B'])]
    D=[(1-i%2,v) for i,v in enumerate(g['D'])]
    chain(P+[old[0]])
    chain([(0,q+4)]+B+[(1,0)])
    chain([(0,0)]+D+[(1,q+1)])
    need(len(adj)==2*(p+q), 'vertex count')
    need(sorted(map(len,adj.values()))==[1,1]+[2]*(2*(p+q)-2), 'degrees')
    result=[];prev=None;at=(0,3)
    while True:
        need(at not in result, 'cycle')
        result.append(at)
        nxt=adj[at]-({prev} if prev is not None else set())
        if not nxt:break
        need(len(nxt)==1, 'branch')
        prev,at=at,next(iter(nxt))
    need(len(result)==len(adj), 'disconnected')
    need([t for t,v in result]==[i%2 for i in range(len(result))], 'orientation')
    out=[v for t,v in result]
    core(out,True)
    COUNTS['graph_insertions']+=1
    return out

def reflect(c):
    p=core(c)
    out=[p-1-x for x in reversed(c)]
    core(out)
    need([p-1-x for x in reversed(out)]==c, 'involution')
    return out

def append(c,r):
    for _ in range(r):
        p=core(c);c=c+[p+x for x in C6]
        core(c)
    return c

def zero_depths(c):return {i+1 for i,v in enumerate(c) if v==0}

def newcore(p,j,s):
    need(p>=16+9*j and 0<=s<=j, 'new core parameters')
    r,delta=divmod(p-16-9*j,6)
    p0=16+delta
    c=SEEDS[p0,PICKS[p0]][:]
    t=next(i for i in range(len(c)-1) if c[i]==c[i+1]==p0-1)
    z=min(i for i,v in enumerate(c) if v==0)
    need(t+1<z, 'max pair before zero')
    b=2*p0-1-t
    for key in ['4']*s+['6']*(j-s):c=extend(c,GADGETS[key],9)
    need(next(i for i in range(len(c)-1) if c[i]==c[i+1]==len(c)//2-1)==t+2*s+4*(j-s), 'max position')
    c=reflect(c)
    need(zero_depths(c)=={b+14*j+2*s,b+14*j+2*s+1}, 'reflected pair')
    c=append(c,r)
    need(len(c)==2*p, 'target size')
    COUNTS['new_final_cores']+=1
    return c

def spider(c,even,n,m,selected,depth,damage=None):
    p=core(c);k=2*p+(4 if even else 3)
    need(n>=2 and m>=0 and 0<=selected<n and depth in zero_depths(c), 'spider parameters')
    M=2*k;A=k if even else k-1;Q=(n-2)*k+m;N=n*k+m
    chosen=[M-x if i%2==0 else x for i,x in enumerate(c)]
    if even:
        chosen += [3*p+5,p+2,3*p+7,p+3]
        other=list(itertools.chain.from_iterable((2*p+5+i,2*p+3-i) for i in range(p)))+[3*p+6,p,3*p+8,p+1]
    else:
        chosen += [3*p+3,p+1,3*p+4]
        other=list(itertools.chain.from_iterable((2*p+3+i,2*p+1-i) for i in range(p)))+[3*p+6,p,3*p+5]
    partner=next(a for a in range(n) if a!=selected)
    labels={('c',0):A}
    for arm,seq in [(selected,chosen),(partner,other)]:
        for t,v in enumerate(seq,1):labels[('a',arm,t)]=v+Q if v>A else v
    for i,arm in enumerate(a for a in range(n) if a not in (selected,partner)):
        for t in range(1,k+1):
            b=(n-2-i)*k-(t-1)//2 if t%2 else i*k+t//2
            labels[('a',arm,t)]=A+b
    for i in range(m):labels[('s',i)]=A+(n-2)*k+i+1
    target=('a',selected,depth)
    if labels[target]==N:labels={v:N-x for v,x in labels.items()}
    if damage=='partial':labels[target]=N
    if damage=='duplicate':labels[('a',partner,k)]=labels[('a',selected,k)]
    if damage=='reverse':
        vals=[labels[('a',selected,t)] for t in range(1,k+1)]
        for t,v in enumerate(reversed(vals),1):labels[('a',selected,t)]=v
    adj=defaultdict(list);edges=[]
    def edge(a,b):edges.append((a,b));adj[a].append(b);adj[b].append(a)
    for arm in range(n):
        previous=('c',0)
        for t in range(1,k+1):
            v=('a',arm,t);edge(previous,v);previous=v
    for i in range(m):edge(('c',0),('s',i))
    need(set(labels)==set(adj), 'actual vertices')
    need(sorted(labels.values())==list(range(N+1)), 'label bijection')
    need(sorted(abs(labels[a]-labels[b]) for a,b in edges)==list(range(1,N+1)), 'edge bijection')
    distances={('c',0):0};queue=deque([('c',0)])
    while queue:
        v=queue.popleft()
        for w in adj[v]:
            if w not in distances:distances[w]=distances[v]+1;queue.append(w)
    need(len(distances)==N+1 and distances[target]==depth and labels[target]==0, 'BFS target')
    COUNTS['actual_spiders']+=1

def gadget(g,q):
    P,B,D=(g[x] for x in ['P','B','D'])
    need(all(len(a)>0 and len(a)%2==0 and min(a)>0 for a in (P,B,D)), 'gadget lengths positivity')
    need(sum(map(len,(P,B,D)))==2*q, 'gadget total size')
    sides=tagged(P)+[(1-i%2,v) for a in (B,D) for i,v in enumerate(a)]
    for t in (0,1):need(sorted(v for u,v in sides if u==t)==list(range(1,q+1)), 'gadget side')
    need(P[0]==3 and B[-1]==4 and D[0]==1, 'gadget anchors')
    chains=[P+[q+3],[q+4]+B+[0],[0]+D+[q+1]]
    need(sorted(a+b for c in chains for a,b in zip(c,c[1:]))==list(range(1,2*q+2))+[2*q+4], 'gadget sums')
    COUNTS['gadget_checks']+=1

def reject(fn):
    try:fn()
    except (ValueError,StopIteration):COUNTS['negative_controls']+=1;return
    raise ValueError('negative control accepted')

def bound(k):
    return 11 if k<35 else 27 if k<53 else 25+16*((k-35)//18)

def main():
    for c in SEEDS.values():core(c,True)
    for c in SMALL.values():core(c)
    for g in GADGETS.values():gadget(g,9)
    gadget(G18,18)
    anchors=[]
    for p,a in PICKS.items():
        c=SEEDS[p,a];anchors.append(min(zero_depths(reflect(c))))
    need(anchors==[26,26,26,26,24,27], 'seed anchors')
    # Exhaust all binary move orders through five steps: tracks both old extrema.
    for p,a in PICKS.items():
        for j in range(6):
            for keys in itertools.product(['4','6'],repeat=j):
                c=SEEDS[p,a][:];b=min(zero_depths(reflect(c)))
                for key in keys:c=extend(c,GADGETS[key],9)
                expected=b+sum(16 if key=='4' else 14 for key in keys)
                need(zero_depths(reflect(c))=={expected,expected+1}, 'all order tracking')
                COUNTS['move_words']+=1
    # All residues, all choices and every common interval position, with positive padding.
    for p in range(25,107):
        U=(p-16)//9;available=set()
        for s in range(U+1):
            c=newcore(p,U,s);available |=zero_depths(c)
            if p in [25,26,30,33,34,35,42,43,44,51,52,53,60,61,62,70,79,88,97,106]:
                for even in (False,True):
                    for n,m in [(2,0),(2,3),(3,0),(4,2),(7,1)]:
                        for arm in set([0,n//2,n-1]):
                            for d in zero_depths(c):spider(c,even,n,m,arm,d)
        need(set(range(27+14*U,26+16*U))<=available, 'common interval')
    # j below U and six-core padding must preserve depth after reflection.
    for p in [34,40,52,70,100,160]:
        for j in range(1,(p-16)//9+1):
            for s in range(j+1):newcore(p,j,s)
    for k in range(19,200001):
        old=11 if k<35 else 27+14*((k-35)//18)+2*(((k-35)//18)//2)
        U=(k-35)//18
        new=old if k<53 else max(old,25+16*U)
        need(new==bound(k) and (k==19 or new>=bound(k-1)), 'piecewise monotonic bound')
        need(new>=old and new<k and 0<=8*k-9*new<=191, 'depth/asymptotic arithmetic')
        if U>=1:need(27+14*U<=old+1, 'interval connection')
        if k>=35:
            p=(k-3)//2 if k%2 else (k-4)//2
            need((p-16)//9==U, 'shell quotient')
        COUNTS['length_arithmetic']+=1
    for d in range(2,10001):
        cutoff=19 if d<=11 else 35 if d<=27 else 35+18*((d-25+15)//16)
        need(bound(cutoff)>=d and (cutoff==19 or bound(cutoff-1)<d), 'inverse boundary')
        COUNTS['inverse_thresholds']+=1
    c=newcore(52,4,2)
    for even in (False,True):
        for kind in ['partial','duplicate','reverse']:
            reject(lambda:spider(c,even,4,2,2,min(zero_depths(c)),kind))
    reject(lambda:core(c[::-1]))
    reject(lambda:core([len(c)//2-x for x in reversed(c)]))
    broken=c[:];broken[1]+=1;reject(lambda:core(broken))
    reject(lambda:spider(c,False,1,0,0,min(zero_depths(c))))
    reject(lambda:spider(c,False,3,0,3,min(zero_depths(c))))
    reject(lambda:spider(c,False,3,0,0,min(zero_depths(c))+2))
    g={k:v[:] for k,v in GADGETS['4'].items()};g['P'][0]=0;reject(lambda:gadget(g,9))
    bindings={name:hashlib.sha256((BASE/name).read_bytes()).hexdigest() for name in ['seeds.json','small-seeds.json','old-data.json','gadget30.json','report.md','manifest.json']}
    print(json.dumps({'status':'PASS','counts':dict(sorted(COUNTS.items())),'seed_pair_starts':anchors,'input_sha256':bindings},sort_keys=True,indent=2))

if __name__=='__main__':main()
