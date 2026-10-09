"""Separate D8 literal, graph, BFS and unbounded-recipe arithmetic audit."""
import hashlib,json,copy
from pathlib import Path
from collections import defaultdict
import core_graph as G

H=Path(__file__).resolve().parent;W=H.parent.parent
AUTHOR=H.parent/'graceful-q10-gap-fill-beyond-d7-2026-10-09-a'
HASHES={'report.md':'3150df1b1f6296c580eebf5c2bc4b7bba9b6ae97436b0ebfbb821f70c41658a6','check.py':'34935d2f44e14eaaaecf992fc5b94e2cfdcee2df8133390d555037cd91bff54e','manifest.json':'ce41485e485b6dd86c92092923326fdaa47095fa8243eb4d733c4531d5d5b685'}
GADGETS={9:G.GADGETS['4'],10:{'P':[3,8],'B':[10,8,9,10,5,5,4,2,3,4],'D':[1,1,2,6,6,7,7,9]},11:{'P':[3,8],'B':[11,10,5,5,4,2,3,4],'D':[1,1,2,6,6,7,7,9,10,8,9,11]}}
need=G.need;COUNTS=defaultdict(int)
EXPECTED=[(62,16,4,1,0,[108,109]),(64,16,3,1,1,[112,113]),(66,16,2,1,2,[116,117]),(68,16,1,1,3,[120,121]),(70,16,0,1,4,[124,125]),(71,17,0,1,4,[124,125]),(71,16,0,0,5,[126,127])]

def F7(p):
    a,r=divmod(p-61,11);return 107+20*a+4*(min(r,9)//2)
def F8(p):
    a,r=divmod(p-61,11);return 107+20*a+2*r
def D7(k):
    return 11 if k<35 else 27 if k<53 else 25+16*((k-35)//18) if k<125 else F7((k-3)//2)
def D8(k):return D7(k) if k<125 else F8((k-3)//2)

def binding():
    for name,expected in HASHES.items():need(hashlib.sha256((AUTHOR/name).read_bytes()).hexdigest()==expected,'exact author hash '+name)
    manifest=json.loads((AUTHOR/'manifest.json').read_text())
    for name,row in manifest.items():
        raw=(AUTHOR/name).read_bytes();need(len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256'],'manifest member '+name)
    for rel,sha in json.loads((AUTHOR/'inputs.json').read_text()).items():need(hashlib.sha256((W/rel).read_bytes()).hexdigest()==sha,'historical binding '+rel)
    return len(manifest)

def build(seed,word):
    c=G.SEEDS[seed,G.PICKS[seed]][:]
    p=G.core(c,True);z=min(i for i,x in enumerate(c) if x==0)
    t=next(i for i in range(len(c)-1) if c[i]==c[i+1]==p-1)
    need(t+1<z,'initial maximum placement')
    b=2*p-1-t
    for q in word:
        c=G.extend(c,GADGETS[q],q)
        p+=q;t+=2
        maxindex=next(i for i in range(len(c)-1) if c[i]==c[i+1]==p-1)
        z=min(i for i,x in enumerate(c) if x==0)
        need(maxindex==t and t+1<z,'maximum tracking')
    out=G.reflect(c)
    expected=b+sum(2*q-2 for q in word)
    need(G.zero_depths(out)=={expected,expected+1},'reflected depths')
    COUNTS['constructed_cores']+=1
    return out

def recipe(row,t):
    need(t>=0 and row['seed'] in (16,17),'recipe parameters')
    p=row['seed']+sum(q*row['q'+str(q)] for q in (9,10,11))
    start=26+sum((2*q-2)*row['q'+str(q)] for q in (9,10,11))
    need(p==row['p'] and row['depths']==[start,start+1],'literal recipe size/depth')
    return p+11*t,[start+20*t,start+20*t+1]

def check_gaps(rows,t):
    coverage=defaultdict(set)
    for row in rows:
        p,ds=recipe(row,t);coverage[p].update(ds)
    for p0 in range(61,72):
        p=p0+11*t
        need(coverage[p]==set(range(F7(p)+1,F8(p)+1)),'exact translated gap coverage')

def reject(fn):
    try:fn()
    except (ValueError,StopIteration):COUNTS['negative_controls']+=1;return
    raise ValueError('negative accepted')

def main():
    payloads=binding()
    seeds=json.loads((AUTHOR/'seeds.json').read_text())
    need([(r['p'],r['d']) for r in seeds]==[(16,16),(17,22)],'literal seed keys')
    for r in seeds:need(r['core']==G.SEEDS[r['p'],r['d']],'exact historical seed copy');G.core(r['core'],True)
    for q,g in GADGETS.items():G.gadget(g,q)
    rows=json.loads((AUTHOR/'recipes.json').read_text())
    need([(r['p'],r['seed'],r['q9'],r['q10'],r['q11'],r['depths']) for r in rows]==EXPECTED,'seven expected rows')
    for t in [0,1,3,8,20]:
        check_gaps(rows,t)
        for row in rows:
            p,depths=recipe(row,t)
            word=[9]*row['q9']+[10]*row['q10']+[11]*(row['q11']+t)
            orders={tuple(word),tuple(reversed(word)),tuple(word[1:]+word[:1])}
            for order in sorted(orders):
                c=build(row['seed'],order)
                need(len(c)==2*p and G.zero_depths(c)==set(depths),'compiled literal recipe')
                for even in [False,True]:
                    for n,m in [(2,0),(2,4),(3,0),(4,3),(7,2)]:
                        for arm in sorted({0,n//2,n-1}):
                            for d in depths:G.spider(c,even,n,m,arm,d);COUNTS['recipe_spiders']+=1
    # Opposite pair orientation is a generic-shell check, not one of the seven recipes.
    for word in [(10,),(11,),(10,11),(11,10),(9,10,11)*3]:
        c=build(21,word)
        need(min(G.zero_depths(c))%2==1,'high-first orientation')
        for even in [False,True]:
            for n,m in [(2,0),(3,5)]:
                for arm in [0,n-1]:
                    for d in G.zero_depths(c):G.spider(c,even,n,m,arm,d);COUNTS['opposite_orientation_spiders']+=1
    gains=[0,2,0,2,0,2,0,2,0,2,4]
    for p in range(61,100001):
        a,r=divmod(p-61,11)
        need(F8(p)-F7(p)==gains[r] and F8(p+11)==F8(p)+20 and F7(p+11)==F7(p)+20,'all residue formula')
        y=p-16;t=(y+10)//11
        need(9*t<=y<=11*t and 2*p-5-2*t==F8(p),'top endpoint intuition')
        COUNTS['size_arithmetic']+=1
    for k in range(19,200001):
        need(D8(k)>=D7(k) and D8(k)<k and 0<=10*k-11*D8(k)<=261,'all k bound')
        if k>19:need(D8(k)>=D8(k-1),'monotone join')
        if k>=125:
            p=(k-3)//2;r=(p-61)%11;epsilon=0 if k%2 else 1
            need(10*k-11*D8(k)==73-2*r+10*epsilon,'tail deficit')
        COUNTS['length_arithmetic']+=1
    for q in (9,10,11):
        bad=copy.deepcopy(GADGETS[q]);bad['P'][0]+=1;reject(lambda:G.gadget(bad,q))
    bad=copy.deepcopy(rows[0]);bad['p']+=1;reject(lambda:recipe(bad,0))
    bad=copy.deepcopy(rows[0]);bad['depths'][0]+=2;reject(lambda:recipe(bad,0))
    reject(lambda:check_gaps(rows[:-2]+rows[-1:],0))
    reject(lambda:check_gaps(rows[:-1],0))
    reject(lambda:G.extend(G.reflect(G.SEEDS[16,16]),GADGETS[10],10))
    c=build(16,(10,11))
    reject(lambda:need(min(G.zero_depths(c))==26+12+10,'ordinary shifts substituted'))
    for even in [False,True]:
        for bad in ['partial','duplicate','reverse']:reject(lambda:G.spider(c,even,4,3,2,min(G.zero_depths(c)),bad))
    reject(lambda:G.spider(c,False,3,0,0,min(G.zero_depths(c))+2))
    reject(lambda:G.spider(c,True,1,0,0,min(G.zero_depths(c))))
    binding()
    print(json.dumps({'status':'PASS','author_payloads':payloads,'counts':dict(COUNTS),'graph_counts':dict(G.COUNTS),'author_bindings':HASHES},indent=2,sort_keys=True))

if __name__=='__main__':main()
