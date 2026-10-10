"""Check all94 interior target rows,51 full paths and exact Lean literal/call links."""
import copy,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
def need(ok,msg):
    if not ok:raise ValueError(msg)
def validate(d):
    need(d['k']==95 and set(d['rows'])=={str(i) for i in range(1,95)},'exact interior target set')
    words=d['words']
    need(len(words)==51 and len({tuple(x) for x in words})==51,'51 distinct words')
    for word in words:
        need(len(word)==191 and sorted(word)==list(range(191)),'path label inventory')
        need(sorted(abs(a-b) for a,b in zip(word,word[1:]))==list(range(1,191)),'path differences')
        need(word[95]==94,'true midpoint')
        need(all((a<=94)!=(b<=94) for a,b in zip(word,word[1:])),'alpha crossing')
    for depth in range(1,95):
        row=d['rows'][str(depth)];word=row['word'];cid=row['certificate']
        need(type(cid) is int and 0<=cid<51 and word==words[cid],'catalog word reference')
        z,q=row['zero_depth'],row['max_depth']
        need(word[95-z]==0 and word[95-q]==190,'catalog extreme positions')
        need(row['part'] in (1,2),'component')
        need(depth==(z if row['part']==1 else q),'chosen physical depth')
def main():
    d=json.loads((HERE/'data/lean-catalog.json').read_text(encoding='utf-8'))
    validate(d)
    literals={}
    for p in sorted((HERE/'source').glob('K95Catalog*.lean')):
        for cid,word in re.findall(r'def path(\d+) : List Nat := (\[[0-9, ]+\])',p.read_text(encoding='utf-8')):
            need(int(cid) not in literals,'duplicate Lean path')
            literals[int(cid)]=json.loads(word)
    need(set(literals)==set(range(51)),'Lean path coverage')
    for i,word in enumerate(d['words']):need(word==literals[i],'Lean literal equality')
    src=(HERE/'source/K95Full.lean').read_text(encoding='utf-8')
    calls=re.findall(r'FiniteAlpha.prescribed_zero 46 (\d+) (\d+) n m K95Catalog.path(\d+) K95Catalog.packet(\d+) hn a\)\.(1|2)',src)
    need(len(calls)==94,'Lean interior calls')
    for depth,call in enumerate(calls,1):
        z,q,c,p,part=map(int,call);row=d['rows'][str(depth)]
        need((z,q,c,p,part)==(row['zero_depth'],row['max_depth'],row['certificate'],row['certificate'],row['part']),'Lean call identity')
    need('K95Boundary.center_zero' in src and 'K95Boundary.leaf_zero' in src and 'K95Tip.tips_prescribed_zero' in src,'boundary cases linked')
    rejected=[]
    for name,mutate in [('omit_depth92',lambda x:x['rows'].pop('92')),('wrong_depth92_component',lambda x:x['rows']['92'].update(part=2)),('wrong_midpoint',lambda x:x['words'][0].__setitem__(95,93)),('phantom_depth95_source',lambda x:x['rows'].update({'95':x['rows']['94']})),('wrong_extreme',lambda x:x['rows']['1'].update(max_depth=2))]:
        x=copy.deepcopy(d);mutate(x)
        try:validate(x)
        except ValueError:rejected.append(name)
        else:raise RuntimeError('ineffective control '+name)
    print(json.dumps({'status':'PASS','interior_depths':94,'distinct_words':51,'literal_and_call_links':94,'rejected_mutants':rejected,'boundary_scope':'hub/leaves/tip linked to source proofs; no new Lean replay'},sort_keys=True))
if __name__=='__main__':main()
