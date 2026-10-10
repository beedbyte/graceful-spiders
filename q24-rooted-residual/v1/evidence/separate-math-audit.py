"""Independent standard-library q24/rooted residual audit; no imported checker."""
from pathlib import Path
from itertools import combinations,product
from collections import Counter
import hashlib,json,sys
P=Path(__file__).resolve().parent;ROOT=P.parents[1];pins={}
def need(x,msg):
    if not x:raise RuntimeError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(rel,h=None):
    z=sha(ROOT/rel)
    if h:need(z==h,'input pin '+rel)
    pins[rel]=z
def load(rel,h):
    pin(rel,h);return json.loads((ROOT/rel).read_text(encoding='utf-8-sig'))
pin('research-audits/graceful-q24-rooted-residual-generalization-2026-10-10-a/report.md','f0fd75067fa68c66c39a6d445e520776fdf0807abca0189e5f1ae6f491454166')
pin('research-audits/graceful-q24-rooted-residual-generalization-2026-10-10-a/manifest.json')
data=load('research-audits/graceful-q24-variable-window-2026-10-10-a/data.json','15e14358c1eef1c88fa168016128f0000b97b804c36b16c9374565f1ba2b642d')
end=load('research-audits/graceful-q24-zero-order-transfer-2026-10-10-a/data.json','8cc56a9ba7a0b9d062ef5d0035e5e6b889671e415ed7c586bfaa90f0427da57d')
for rel,h in {
 'graceful-q24-zero-order-transfer-2026-10-10-a/report.md':'469a6167c41653138a227527d6e56f8c229133df71ce63446fad1d5f153ac729',
 'graceful-q24-flipped-zero-independent-2026-10-10-a/report.md':'efc0e5ee50b6e214c81396d8523c8fc5fd84e99c9d28e0f488fbc49a6c57ed1e',
 'graceful-k71-rooted-residual-formal-2026-10-10-a/source/RootedInjective.lean':'688e8761808978138bf749497295928d13a3e7903bdd21f95ab2c78f22d5f186',
 'graceful-q24-zero-order-formal-2026-10-10-a/source/Q24Terminal.lean':'088fd226e1c2adb57556ebd1fc047ba8494546511cb8096d4d089f679aefcc91',
 'graceful-k71-rooted-residual-transfer-2026-10-10-a/report.md':'244d88c994f6978bd49bd56a53264658788068586f487c15fa03ad928de499dc',
 'graceful-k71-rooted-residual-transfer-2026-10-10-a/ERRATUM.md':'5301e6c10372c574b0326cf11979688c57e747d98cd1337e12fc93e6b3673338'}.items():pin('research-audits/'+rel,h)
def inventory(x,k):
    need(len(x)==2*k+1,'offset length')
    need(sorted(x[::2])==list(range(k+1)) and sorted(x[1::2])==list(range(k)),'offset side bands')
    need(sorted(a+b for a,b in zip(x,x[1:]))==list(range(2*k)),'offset edge sums')
    need(x[k]==k-1,'offset midpoint')
def source_state(x,k,z):
    inventory(x,k)
    need(z%2==1 and z+2<k and x[z-1:z+3]==[1,0,0,2] and x[-1]==12,'normal source window')
def gadget_contract(g,odd):
    B,D,A=g['B'],g['D'],g['A']
    need(len(B)+len(D)==24 and len(A)==24 and len(B)%2==odd,'gadget lengths/parity')
    # B and A start low; D starts high exactly for the odd B1 step.
    high=B[1::2]+D[(0 if odd else 1)::2]+A[1::2]
    low=B[::2]+D[(1 if odd else 0)::2]+A[::2]
    need(sorted(high)==list(range(1,25)) and sorted(low)==list(range(1,25)),'gadget fresh side inventories')
    chains=[[25]+B+[0],[0]+D+[26],[36]+A]
    need(sorted(a+b for c in chains for a,b in zip(c,c[1:]))==list(range(1,51)),'gadget exact seam sums')
def step(x,z,g):return [v+24 for v in x[:z]]+g['B']+[0,0]+g['D']+[v+24 for v in x[z+2:]]+g['A']
def path(t):
    need(t>=1,'terminal t domain')
    x=data['seed'].copy();k=23;z=3;source_state(x,k,z)
    for _ in range(t-1):
        x=step(x,z,data['gadgets']['2']);k+=24;z+=2;source_state(x,k,z)
    y=step(x,z,end);K=k+24;inventory(y,K)
    need(y[z+1:z+3]==[0,0] and (z+1)%2==0,'terminal high/low zero order')
    w=[2*K-v if i%2==0 else v for i,v in enumerate(y)]
    need(sorted(w)==list(range(2*K+1)),'path full label band')
    need(sorted(abs(a-b) for a,b in zip(w,w[1:]))==list(range(1,2*K+1)),'path full weights')
    need(w[K]==K-1 and all((a<=K-1<b) or (b<=K-1<a) for a,b in zip(w,w[1:])),'path actual midpoint/alpha')
    need(w[K-(20+22*t)]==0 and w[K-(21+22*t)]==2*K,'both exact physical targets')
    return w
gadget_contract(data['gadgets']['2'],0);gadget_contract(end,1)
def residual(labels,edges,root_label=0):
    # Label zero need not be the first indexed vertex.
    keys=['named-'+str(len(labels)-i-1) for i in range(len(labels))]
    g=dict(zip(keys,labels));E=[(keys[a],keys[b]) for a,b in edges]
    root=keys[labels.index(root_label)]
    return {'vertices':keys,'edges':E,'g':g,'root':root,'Q':len(E)}
def conventional(H,root_zero=True):
    V,E,g,Q,r=H['vertices'],H['edges'],H['g'],H['Q'],H['root']
    need(len(E)==Q and len(V)==len(set(V)) and set(g)==set(V),'finite indexed graph identity')
    need(r in V and all(u in g and v in g for u,v in E),'actual graph/root endpoints')
    need(len(set(g.values()))==len(V) and all(0<=x<=Q for x in g.values()),'conventional injective vertex band')
    need(sorted(abs(g[u]-g[v]) for u,v in E)==list(range(1,Q+1)),'conventional bijective edge inventory')
    if root_zero:need(g[r]==0,'specified root zero')
def graft(w,H,side,depth,complement=False,shift=True,matching_translation=False):
    if side=='right':w=w[::-1]
    K=(len(w)-1)//2;M=2*K;A=w[K];Q=H['Q'];N=M+Q
    V=[('H',v) for v in H['vertices']]+[(s,d) for s in ('left','right') for d in range(1,K+1)]
    root=('H',H['root']);E=[(('H',u),('H',v)) for u,v in H['edges']]
    E += [(root if d==1 else (s,d-1),(s,d)) for s in ('left','right') for d in range(1,K+1)]
    delta=A-H['g'][H['root']] if matching_translation else A
    f={('H',v):delta+H['g'][v] for v in H['vertices']}
    if not matching_translation:need(f[root]==A,'root/midpoint seam equality')
    for s,sgn in (('left',-1),('right',1)):
        for d in range(1,K+1):
            x=w[K+sgn*d];f[s,d]=x+(Q if shift and x>A else 0)
    if complement:f={v:N-x for v,x in f.items()}
    return V,E,f,(side,depth),N
def output_check(out,target_zero=True):
    V,E,f,target,N=out
    need(set(f)==set(V) and len(E)==N,'exact output topology/cardinality')
    need(len(set(f.values()))==len(V) and all(0<=x<=N for x in f.values()),'output injective band')
    need(sorted(abs(f[u]-f[v]) for u,v in E)==list(range(1,N+1)),'output complete edge inventory')
    if target_zero:need(f[target]==0,'actual named target zero')
    return sorted(f.values())==list(range(N+1))
named={
 'singleton':residual([0],[]),
 'one_edge':residual([1,0],[(0,1)]),
 'star3':residual([3,2,0,1],[(2,0),(2,1),(2,3)]),
 'P4_branch_at_inner_zero':residual([3,0,2,1],[(0,1),(1,2),(2,3)]),
 'triangle_nononto':residual([3,0,1],[(0,1),(1,2),(2,0)]),
 'triangle_plus_isolated_onto':residual([3,2,0,1],[(0,2),(2,3),(3,0)])}
for H in named.values():conventional(H)
paths={t:path(t) for t in (1,2,3,7,17)}
graphs=edges=onto=nononto=0
for t,w in paths.items():
    for name,H in named.items():
        for side in ('left','right'):
            for d,mx in ((20+22*t,False),(21+22*t,True)):
                out=graft(w,H,side,d,mx);isonto=output_check(out)
                need(isonto==(sorted(H['g'].values())==list(range(H['Q']+1))),'onto iff residual onto')
                graphs+=1;edges+=len(out[1]);onto+=isonto;nononto+=not isonto
# Exhaustive literal graceful residual instances with Q<=5. Each indexed vertex
# set is a subset of 0..Q containing 0; choose one edge of every weight.
bounded=[]
for Q in range(6):
    for bits in product((False,True),repeat=Q):
        labels=[0]+[i+1 for i,b in enumerate(bits) if b]
        choices=[[(i,j) for i,j in combinations(range(len(labels)),2) if abs(labels[i]-labels[j])==d] for d in range(1,Q+1)]
        if any(not x for x in choices):continue
        for E in product(*choices):
            H=residual(labels,list(E));conventional(H);bounded.append(H)
bounded_graphs=bounded_edges=0
for H in bounded:
    for side in ('left','right'):
        for d,mx in ((42,False),(43,True)):
            out=graft(paths[1],H,side,d,mx);output_check(out)
            bounded_graphs+=1;bounded_edges+=len(out[1])
mutants=[]
def rejects(name,fn):
    try:fn()
    except RuntimeError:mutants.append(name)
    else:raise RuntimeError('mutant escaped '+name)
w=paths[1];H=named['triangle_nononto']
rejects('omit high-side Q shift',lambda:output_check(graft(w,H,'left',42,shift=False)))
rejects('omit whole complement for maximum',lambda:output_check(graft(w,H,'right',43)))
out=graft(w,H,'right',43,True);V,E,f,target,N=out
partial={v:(N-x if v[0]!='H' else x) for v,x in graft(w,H,'right',43)[2].items()}
rejects('complement only new arms',lambda:output_check((V,E,partial,target,N)))
rejects('wrong named target arm',lambda:output_check((V,E,f,('left',43),N)))
rejects('wrong physical depth',lambda:output_check((V,E,f,('right',42),N)))
rejects('omit one residual edge',lambda:output_check((V,E[1:],f,target,N)))
rejects('false full vertex band for triangle',lambda:need(output_check(out),'triangle output not onto'))
edge_nonzero=residual([0,1],[(0,1)],1)
rejects('arbitrary fixed nonzero root',lambda:output_check(graft(w,edge_nonzero,'left',42)))
rejects('match nonzero root by translating residual',lambda:output_check(graft(w,edge_nonzero,'left',42,matching_translation=True)))
interior=residual([0,3,1,2],[(0,1),(1,2),(2,3)],1)
conventional(interior,False)
rejects('alpha residual interior specified root',lambda:output_check(graft(w,interior,'left',42,matching_translation=True)))
nonalpha=[0,4,1,3,2]
need(sorted(nonalpha)==list(range(5)) and sorted(abs(a-b) for a,b in zip(nonalpha,nonalpha[1:]))==list(range(1,5)) and nonalpha[2]==1,'nonalpha graceful midpoint example')
rejects('graceful midpoint source without alpha',lambda:output_check(graft(nonalpha,named['one_edge'],'left',2)))
duplicate={'vertices':['r','a','isolated'],'edges':[('r','a')],'g':{'r':0,'a':1,'isolated':0},'root':'r','Q':1}
rejects('drop residual vertex injectivity',lambda:output_check(graft(w,duplicate,'left',42)))
rejects('t0 falsely admitted',lambda:path(0))
# Root maximum is a valid alternative hypothesis only after normalizing H.
maxroot=residual([0,1],[(0,1)],1)
maxroot['g']={v:1-x for v,x in maxroot['g'].items()};conventional(maxroot)
for side in ('left','right'):
    for d,mx in ((42,False),(43,True)):output_check(graft(w,maxroot,side,d,mx))
result={'status':'MATHEMATICAL_GO_SCOPED_ROOT_ZERO_CONVENTIONAL_GRAFT','input_pins':pins,'source_parameters':list(paths),'named_residuals':list(named),
 'named_grafts':graphs,'named_edges':edges,'onto_cases':onto,'nononto_cases':nononto,'bounded_residual_instances':len(bounded),'bounded_grafts':bounded_graphs,'bounded_edges':bounded_edges,
 'root_maximum_normalized_cases':4,'mutants_rejected':mutants,'python_executable':sys.executable,'python_sha256':sha(Path(sys.executable)),
 'path_words':{str(t):{'K':(len(w)-1)//2,'low_zero_depth':20+22*t,'high_zero_depth':21+22*t,'canonical_sha256':hashlib.sha256(json.dumps(w,separators=(',',':')).encode()).hexdigest()} for t,w in paths.items()}}
(P/'input-pins.json').write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2,sort_keys=True))
