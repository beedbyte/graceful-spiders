"""Separate recipe-level induction and graph/BFS audit for the 10/11 candidate."""
import json,hashlib
from pathlib import Path
from collections import defaultdict
from functools import lru_cache
import core_graph as G

H=Path(__file__).resolve().parent
Q11={'P':[3,8],'B':[11,10,5,5,4,2,3,4],'D':[1,1,2,6,6,7,7,9,10,8,9,11]}
MOVES={'A':(9,14),'B':(9,16),'C':(11,20),'P':(6,0)}
need=G.need
COUNTS=defaultdict(int)

def F(p):
    a,r=divmod(p-61,11)
    return 107+20*a+4*(min(r,9)//2)

def D6(k):return 11 if k<35 else 27 if k<53 else 25+16*((k-35)//18)
def D7(k):return D6(k) if k<=124 else F((k-3)//2)

def base_recipes():
    reachable={p:{} for p in range(16,72)}
    for p,d in G.PICKS.items():
        b=min(G.zero_depths(G.reflect(G.SEEDS[p,d])))
        reachable[p][b]=(p,'')
    for p in range(16,72):
        for b,(seed,word) in list(reachable[p].items()):
            for name,(q,gain) in MOVES.items():
                if p+q<72:reachable[p+q].setdefault(b+gain,(seed,word+name))
    bases={}
    for p in range(61,72):
        for d in range(83,F(p)+1):
            key=d if d in reachable[p] else d-1
            need(key in reachable[p],'base coverage')
            bases[p,d]=reachable[p][key]
    return bases

BASES=base_recipes()

@lru_cache(maxsize=None)
def recipe(p,d):
    need(p>=61 and 83<=d<=F(p),'induction input')
    if p<=71:return BASES[p,d]
    need(F(p)==F(p-11)+20 and F(p-6)>=102,'induction intervals')
    if d<=F(p-6):
        s,w=recipe(p-6,d);return s,w+'P'
    need(83<=d-20<=F(p-11),'shifted branch')
    s,w=recipe(p-11,d-20);return s,w+'C'

def compile_recipe(p,d,rec):
    seed,word=rec
    c=G.SEEDS[seed,G.PICKS[seed]][:]
    b=min(G.zero_depths(G.reflect(c)))
    need(p==seed+sum(MOVES[x][0] for x in word),'recipe size')
    start=b+sum(MOVES[x][1] for x in word)
    need(d in [start,start+1],'recipe target arithmetic')
    for move in word:
        if move=='P':continue
        q,gain=MOVES[move]
        gadget=Q11 if move=='C' else G.GADGETS['6' if move=='A' else '4']
        c=G.extend(c,gadget,q)
    c=G.append(G.reflect(c),word.count('P'))
    need(G.core(c)==p and G.zero_depths(c)=={start,start+1} and d in G.zero_depths(c),'compiled recipe')
    COUNTS['compiled_recipes']+=1
    return c

def reject(fn):
    try:fn()
    except (ValueError,StopIteration):COUNTS['negative_controls']+=1;return
    raise ValueError('negative accepted')

def main():
    G.gadget(Q11,11)
    for p,d in G.PICKS.items():G.core(G.SEEDS[p,d],True)
    certificates=[]
    for (p,d),rec in BASES.items():
        c=compile_recipe(p,d,rec)
        certificates.append({'p':p,'d':d,'seed':rec[0],'word':rec[1],'core':c})
        for even in [False,True]:
            for n,m in [(2,0),(3,2),(5,0)]:
                for arm in [0,n-1]:
                    G.spider(c,even,n,m,arm,d);COUNTS['base_spiders']+=1
    for p in list(range(72,161))+[172,183,200,250,500]:
        for d in sorted({83,103,F(p-6),F(p-6)+1,F(p)}):
            if 83<=d<=F(p):
                c=compile_recipe(p,d,recipe(p,d))
                for even in [False,True]:
                    G.spider(c,even,4,3,2,d);COUNTS['induction_spiders']+=1
    for p in range(61,100001):
        need(F(p)<2*p+3,'legal depth')
        if p>=72:need(F(p)==F(p-11)+20 and F(p-6)>=115,'symbolic induction check')
        need(F(p)>=D6(2*p+3),'nonregression')
        COUNTS['size_arithmetic']+=1
    # a=9q+s reduces comparison with D6 to this complete 9x11 residue table.
    comparison=[]
    for s in range(9):
        for r in range(11):
            gap=2+20*s+4*(min(r,9)//2)-16*((11*s+r)//9)
            need(gap>=2,'finite nonregression residue');comparison.append(gap)
    for k in range(19,200001):
        need(D7(k)>=D6(k) and D7(k)<k and 0<=10*k-11*D7(k)<=261,'all-k arithmetic')
        if k>19:need(D7(k)>=D7(k-1),'monotonic bound')
        COUNTS['length_arithmetic']+=1
    c=compile_recipe(72,F(72),recipe(72,F(72)))
    reject(lambda:G.extend(G.reflect(G.SEEDS[16,16]),Q11,11))
    reject(lambda:compile_recipe(72,F(72), (16,'CCCC')))
    reject(lambda:recipe(60,83))
    reject(lambda:recipe(72,F(72)+1))
    bad={k:v[:] for k,v in Q11.items()};bad['P'][1]+=1;reject(lambda:G.gadget(bad,11))
    pre=G.extend(G.SEEDS[16,16],Q11,11)
    right=G.append(G.reflect(pre),1)
    wrong=G.reflect(G.append(pre,1))
    reject(lambda:need(G.zero_depths(wrong)==G.zero_depths(right),'append order'))
    reject(lambda:need(min(G.zero_depths(G.reflect(pre)))==36,'ordinary versus reflected shift'))
    for even in [False,True]:
        for bad in ['partial','duplicate','reverse']:
            reject(lambda:G.spider(c,even,4,3,2,F(72),bad))
    body=json.dumps(certificates,sort_keys=True,separators=(',',':'))+'\n'
    if '--write-base-certificates' in __import__('sys').argv:
        (H/'base-certificates.json').write_text(body,encoding='utf-8')
    else:
        need((H/'base-certificates.json').read_text(encoding='utf-8')==body,'saved base certificate exactness')
    print(json.dumps({'status':'PASS','counts':dict(COUNTS),'base_depth_certificates':len(BASES),'base_interval':[83,'F(p)'],'nonregression_minimum_residue_gap':min(comparison),'graph_counts':dict(G.COUNTS),'base_certificates_sha256':hashlib.sha256(body.encode()).hexdigest()},indent=2,sort_keys=True))

if __name__=='__main__':main()
