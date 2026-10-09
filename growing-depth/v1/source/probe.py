"""Bounded whole-arm normalized-sum search; no old D-prefix invariants."""
import json,sys,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'graceful-k13-next-2026-10-09'/'vendor'))
from ortools.sat.python import cp_model

def solve(r,depth,seconds=8):
    model=cp_model.CpModel()
    hs=list(range(r))+[r+1]
    h=[model.new_int_var_from_domain(cp_model.Domain.from_values(hs),f'h{i}') for i in range(r+1)]
    l=[model.new_int_var(0,r-1,f'l{i}') for i in range(r)]
    e=[model.new_int_var(0,2*r-1,f'e{i}') for i in range(2*r)]
    model.add_all_different(h);model.add_all_different(l);model.add_all_different(e)
    model.add(h[0]==1);model.add(h[-1]==r+1)
    model.add(l[depth//2-1]==0);model.add(h[depth//2]==0)
    for i in range(r):
        model.add(e[2*i]==h[i]+l[i])
        model.add(e[2*i+1]==l[i]+h[i+1])
    solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=seconds
    solver.parameters.num_search_workers=1;solver.parameters.random_seed=1
    status=solver.solve(model)
    row={'r':r,'k':2*r+1,'depth':depth,'status':solver.status_name(status),'seconds':solver.wall_time}
    if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
        row['h']=[solver.value(v) for v in h];row['l']=[solver.value(v) for v in l]
        row['sums']=[solver.value(v) for v in e]
    return row

if __name__=='__main__':
    rows=[]
    for r in (7,8,9,10,11,12,14,17):
        row=solve(r,8);rows.append(row);print(json.dumps(row),flush=True)
    Path(__file__).with_name('probe-results.json').write_text(json.dumps(rows,indent=2)+'\n')
