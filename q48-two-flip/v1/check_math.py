"""Independent generalized phase, two-flip, and actual-graph checks."""
from pathlib import Path
from collections import Counter
import json,hashlib,copy
P=Path(__file__).resolve().parent
def need(v,s):
 if not v:raise ValueError(s)
def inv(xs,lo,hi):need(Counter(xs)==Counter(range(lo,hi+1)),'inventory')
def sums(x):return [a+b for a,b in zip(x,x[1:])]
def path(x):
 k=len(x)//2;need(len(x)==2*k+1 and k%2==1,'odd length')
 inv(x[::2],0,k);inv(x[1::2],0,k-1);inv(sums(x),0,2*k-1)
 need(x[k]==k-1,'physical midpoint')
 w=[2*k-v if i%2==0 else v for i,v in enumerate(x)]
 inv(w,0,2*k);inv([abs(a-b) for a,b in zip(w,w[1:])],1,2*k)
 need(all((a<k)!=(b<k) for a,b in zip(w,w[1:])),'alpha cut')
 return w
def contract(g,p,a,b,e,r):
 B,D,A=g['B'],g['D'],g['A']
 need((len(B),len(D),len(A))==(r,24-r,24),'lengths')
 sides=[[],[]]
 for values,start in [(B,p),(D,(p+r)%2),(A,1)]:
  for i,v in enumerate(values):sides[(start+i)%2].append(v)
 for side in sides:inv(side,1,24)
 bands=[sums([24+a]+B+[0]),sums([0]+D+[24+b]),sums([24+e]+A)]
 need(Counter(sum(bands,[]))==Counter(list(range(1,49))+[48+a,48+b]),'chain sums')
 need(A[-1]==e,'terminal')
 return bands
def step(x,g,p,a,b,e,r):
 path(x);z=x.index(0);k=len(x)//2
 need(z%2==p and 1<=z and z+2<k,'input tag/window domain')
 need(x[z-1:z+3]==[a,0,0,b] and x[-1]==e,'input anchors')
 contract(g,p,a,b,e,r)
 y=[v+24 for v in x[:z]]+g['B']+[0,0]+g['D']+[v+24 for v in x[z+2:]]+g['A']
 path(y);return y
def family(base,old,first,second,t):
 need(type(t)==int and t>=2,'t domain')
 x=base[:]
 for _ in range(t-2):x=step(x,old,1,1,2,12,2)
 x=step(x,first,1,1,2,12,1)
 return step(x,second,0,12,1,12,1)
def macro(first,second):
 return {'B':[v+24 for v in first['B']]+second['B'],
         'D':second['D']+[v+24 for v in first['D']],
         'A':[v+24 for v in first['A']]+second['A']}
def macro_contract(g):
 B,D,A=g['B'],g['D'],g['A'];need((len(B),len(D),len(A))==(2,46,48),'macro lengths')
 inv(B[::2]+D[::2]+A[::2],1,48);inv(B[1::2]+D[1::2]+A[1::2],1,48)
 bands=[sums([49]+B+[0]),sums([0]+D+[50]),sums([60]+A)]
 inv(sum(bands,[]),1,98);need(A[-1]==12,'macro terminal');return bands
def macro_step(x,g):
 z=x.index(0)
 return [v+48 for v in x[:z]]+g['B']+[0,0]+g['D']+[v+48 for v in x[z+2:]]+g['A']
def residual(arms,k,m):
 h=len(arms);f={('hub',):0}
 for i,a in enumerate(arms):
  for d in range(1,k+1):f['arm',a,d]=k*(h-i)-(d-1)//2 if d%2 else k*i+d//2
 for j in range(m):f['leaf',j]=h*k+j+1
 return f
def graph(w,n,m,a,flip):
 k=len(w)//2;b=(a+1)%n;Q=k*(n-2)+m;N=k*n+m
 need(n>=2 and m>=0 and 0<=a<n,'graph domain')
 f={v:z+k-1 for v,z in residual([i for i in range(n) if i not in (a,b)],k,m).items()}
 for arm,sign in [(a,-1),(b,1)]:
  for d in range(1,k+1):
   z=w[k+sign*d];f['arm',arm,d]=z+(Q if z>=k else 0)
 return {v:N-z for v,z in f.items()} if flip else f
def graph_check(f,k,n,m,a,d):
 vs={('hub',)}|{('arm',i,j) for i in range(n) for j in range(1,k+1)}|{('leaf',j) for j in range(m)}
 need(set(f)==vs,'named vertices');inv(f.values(),0,k*n+m)
 es=[(('hub',) if j==1 else ('arm',i,j-1),('arm',i,j)) for i in range(n) for j in range(1,k+1)]+[(('hub',),('leaf',j)) for j in range(m)]
 inv([abs(f[u]-f[v]) for u,v in es],1,k*n+m);need(f['arm',a,d]==0,'named target');return len(es)
def run():
 data=json.loads((P/'data.json').read_text());base,old,first,second=(data[x] for x in ['seed','old','first','second'])
 need(first['B']==[12] and second['B']==[13],'candidate singleton values')
 band1=contract(first,1,1,2,12,1);band2=contract(second,0,12,1,12,1)
 combined=macro(first,second);macro_bands=macro_contract(combined)
 need(first['D'][0]==second['D'][0]==1 and second['A'][0]==24,'forced small/max sums')
 selected=[];count={'sources':0,'graphs':0,'edges':0};x=base[:]
 for t in range(2,102):
  mid=step(x,first,1,1,2,12,1);z=mid.index(0)
  need(mid[z-1:z+3]==[12,0,0,1] and z%2==0,'intermediate reverse window')
  y=step(mid,second,0,12,1,12,1);w=path(y);k=23+24*t
  need(y==macro_step(x,combined),'complete composite list identity')
  need(len(y)==2*k+1 and w.index(0)==2*t+1 and w.index(2*k)==2*t+2,'final index/depth')
  need(y[y.index(0)-1:y.index(0)+3]==[13,0,0,1],'final forward window')
  count['sources']+=1
  if t in [2,3,5,6]:
   selected.append({'t':t,'k':k,'offsets':y,'low_zero_depth':22+22*t,'high_zero_depth':21+22*t})
   for n,m in [(2,0),(2,1),(3,0),(3,2),(5,1)]:
    for a in range(n):
     for flip in [False,True]:
      f=graph(w,n,m,a,flip);d=22+22*t-int(flip)
      count['edges']+=graph_check(f,k,n,m,a,d);count['graphs']+=1
  x=step(x,old,1,1,2,12,2)
 examples=json.loads((P/'examples.json').read_text())
 comparisons=[]
 for row in examples:
  own=next(v for v in selected if v['t']==row['t'])
  need(own['offsets']==row['offsets'],'complete author example comparison')
  need(own['k']==row['k'] and own['low_zero_depth']==row['direct_zero_depth'] and own['high_zero_depth']==row['complement_zero_depth'],'author metadata comparison')
  need(row['low_zero_index']==2*row['t']+1 and row['high_zero_index']==2*row['t']+2,'author index comparison')
  comparisons.append(row['t'])
 rejected=[]
 def reject(name,fn):
  try:fn()
  except (ValueError,KeyError):rejected.append(name)
  else:raise RuntimeError('survived '+name)
 for which,g,pars in [('first',first,(1,1,2,12,1)),('second',second,(0,12,1,12,1))]:
  for part in ['B','D','A']:
   bad=copy.deepcopy(g);bad[part][0]+=1;reject('corrupt '+which+' '+part,lambda bad=bad,pars=pars:contract(bad,*pars))
 reject('second false contiguous1..50',lambda:inv(sum(band2,[]),1,50))
 reject('wrong second phase',lambda:contract(second,1,12,1,12,1))
 reject('wrong second input anchors',lambda:contract(second,0,1,2,12,1))
 reject('swap flip order',lambda:family(base,old,second,first,2))
 mid=step(base,first,1,1,2,12,1)
 reject('repeat first flip',lambda:step(mid,first,1,1,2,12,1))
 reject('t1',lambda:family(base,old,first,second,1))
 for name,part in [('wrong macro D order','D'),('unshifted first A','A'),('wrong macro B shift','B')]:
  bad=copy.deepcopy(combined)
  if part=='D':bad[part]=[v+24 for v in first['D']]+second['D']
  elif part=='A':bad[part]=first['A']+second['A']
  else:bad[part][0]-=1
  reject(name,lambda bad=bad:macro_contract(bad))
 y=family(base,old,first,second,2);w=path(y);bad=y[:];bad[71]+=1
 reject('midpoint',lambda:path(bad))
 f=graph(w,2,0,0,False);reject('incorrect target65',lambda:graph_check(f,71,2,0,0,65))
 f=graph(w,2,0,0,True);reject('incorrect direct/complement assignment',lambda:graph_check(f,71,2,0,0,66))
 f=graph(w,3,2,1,False);reject('wrong named arm',lambda:graph_check(f,71,3,2,0,66))
 f=graph(w,2,0,0,False);f['leaf',0]=0;reject('phantom m0 leaf',lambda:graph_check(f,71,2,0,0,66))
 f=graph(w,2,1,0,False);del f['leaf',0];reject('omitted original leaf',lambda:graph_check(f,71,2,1,0,66))
 f=graph(w,3,1,0,False)
 for d in range(1,72):f['arm',0,d]=214-f['arm',0,d]
 reject('only selected arm complemented',lambda:graph_check(f,71,3,1,0,65))
 return {'status':'PASS','counts':count,'first_chain_sums':band1,'second_chain_sums':band2,'composite':combined,'composite_chain_sums':macro_bands,'selected_sources':selected,'author_complete_example_matches':comparisons,'mutants':rejected,'scope':'conditional general contract plus checked frozen two literals; all t>=2 by proof'}
if __name__=='__main__':print(json.dumps(run(),indent=2))
