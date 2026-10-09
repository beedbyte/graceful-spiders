"""Check exact frozen author tables without reading or running author code."""
import json,hashlib
from pathlib import Path
import audit as A
G=A.G;need=A.need
ROOT=Path(__file__).resolve().parent.parent
AUTHOR=ROOT/'graceful-ten-elevenths-global-2026-10-09-a'
HASHES={'report.md':'bf7eec616fa42a5465703e4f90d296f02dcb35a0b91c5c6c82bdfcf5208f9249','manifest.json':'419634baa520139e83395fb2014478710317d8bf72f83c4c7c54e31083be739d','verify.py':'8d3e1321bdbbf1477d86b8fa0ad4816555dd9897735fbefec82024347b2c38d2'}

def K7(d):
    if d<=11:return 19
    if d<=27:return 35
    if d<=89:return 35+18*((d-25+15)//16)
    a=max(0,-((123-d)//20));s=max(0,-((107+20*a-d)//4))
    need(s<=4,'inverse plateau range')
    return 125+22*a+4*s

def table(row):
    p,a,j,delta,h=(row[x] for x in ['p','a','j','delta','padding'])
    need(h==0 and 0<=delta<=5 and a>=0 and j>=0,'literal table parameters')
    b=[26,26,26,26,24,27][delta]
    need(p==16+delta+11*a+9*j+6*h,'literal table size')
    lo,hi=b+20*a+14*j,b+20*a+16*j+1
    need(row['lo']==lo and row['hi']==hi,'literal interval')
    return set(range(lo,hi+1))

def main():
    for name,sha in HASHES.items():need(hashlib.sha256((AUTHOR/name).read_bytes()).hexdigest()==sha,'author binding '+name)
    manifest=json.loads((AUTHOR/'manifest.json').read_text())['files']
    for name,row in manifest.items():
        b=(AUTHOR/name).read_bytes();need(len(b)==row['bytes'] and hashlib.sha256(b).hexdigest()==row['sha256'],'manifest member')
    need((AUTHOR/'verification-normal.json').read_bytes()==(AUTHOR/'verification-optimized.json').read_bytes(),'author saved modes')
    data=json.loads((AUTHOR/'verification-normal.json').read_text())
    need(set(map(int,data['bases']))==set(range(61,67)),'six base table sizes')
    need(set(map(int,data['bridges']))==set(range(67,78)),'eleven bridge table sizes')
    checked=0;spiders=0;recipes=0
    for kind in ['bases','bridges']:
        for key,rows in data[kind].items():
            p=int(key);covered=set()
            for row in rows:
                need(row['p']==p,'table row key');covered|=table(row)
                for t in [0,1,7]:
                    p2=p+11*t
                    for s in range(row['j']+1):
                        word='C'*(row['a']+t)+'B'*s+'A'*(row['j']-s)
                        seed=16+row['delta'];b=[26,26,26,26,24,27][row['delta']]
                        d=b+20*(row['a']+t)+14*row['j']+2*s
                        c=A.compile_recipe(p2,d,(seed,word));recipes+=1
                        for depth in [d,d+1]:
                            for even in [False,True]:
                                for n,m in [(2,0),(3,2),(5,0)]:
                                    for arm in [0,n-1]:G.spider(c,even,n,m,arm,depth);spiders+=1
            low=106 if kind=='bases' else A.F(p-6)+1
            need(set(range(low,A.F(p)+1))<=covered,'literal interval chain coverage')
            checked+=1
    # Independent finite modular proof for optional recipe-family exactness.
    cvals=[11*b+11-320-20*i for i,b in enumerate([26,26,26,26,24,27])]
    need(cvals==[-23,-43,-63,-83,-125,-112],'endpoint constants')
    above=[]
    for r in range(11):
        p=61+r;defect=11*A.F(p)-20*p
        need(-71<defect,'large j or positive padding excluded')
        candidates=[]
        for delta in range(6):
            for j in range(12):
                if (16+delta+9*j-p)%11==0 and cvals[delta]-4*j>defect:candidates.append((delta,j,cvals[delta]-4*j-defect))
        need(candidates==([(0,0,44)] if p%11==5 else []),'modular high candidates')
        above.append(candidates)
    for d in range(2,100001):
        k=K7(d);need(A.D7(k)>=d and (k==19 or A.D7(k-1)<d),'inverse cutoff')
    rejected=0
    bad=dict(data['bridges']['67'][0]);bad['hi']+=1
    try:table(bad)
    except ValueError:rejected+=1
    else:raise ValueError('bad interval accepted')
    bad=dict(data['bridges']['77'][-1]);bad['delta']=(bad['delta']+1)%6
    try:table(bad)
    except ValueError:rejected+=1
    else:raise ValueError('bad residue accepted')
    need(rejected==2,'table negative controls')
    print(json.dumps({'status':'PASS','author_manifest_members':len(manifest),'interval_table_rows':checked,'constructed_table_recipes':recipes,'actual_spiders':spiders,'inverse_thresholds':99999,'modular_candidate_tests':72*11,'negative_controls':rejected,'source_bindings':HASHES},sort_keys=True,indent=2))

if __name__=='__main__':main()
