"""Check the fixed local certificate and its literal identity with Lean; no solver."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def check(d):
    B, D, A = (d[x] for x in ('B','D','A'))
    need((len(B),len(D),len(A)) == (1,23,24), 'block lengths')
    need(all(type(x) is int and 1<=x<=24 for v in (B,D,A) for x in v), 'offset domain')
    need(A[-1] == 12, 'terminal')
    need(sorted(D[::2]+A[1::2]) == list(range(1,25)), 'high side')
    need(sorted(B+D[1::2]+A[::2]) == list(range(1,25)), 'low side')
    chains = ([25]+B+[0], [0]+D+[26], [36]+A)
    sums = [x+y for chain in chains for x,y in zip(chain,chain[1:])]
    need(sorted(sums) == list(range(1,51)), 'three-chain sums')

def main():
    raw = (HERE/'data/gadget.json').read_bytes()
    need(hashlib.sha256(raw).hexdigest() == '8cc56a9ba7a0b9d062ef5d0035e5e6b889671e415ed7c586bfaa90f0427da57d', 'frozen literal hash')
    d = json.loads(raw)
    source = (HERE/'source/Q24Terminal.lean').read_text(encoding='utf-8')
    for key in ('B','D','A'):
        match = re.search(r'def '+key+r' : List Nat := (\[[0-9, ]+\])', source)
        need(match is not None and json.loads(match[1]) == d[key], 'Lean literal '+key)
    check(d)
    rejected = []
    for key,index,value in [('B',0,15),('D',0,2),('D',22,22),('A',0,13),('A',23,11)]:
        mutant = {k:list(v) for k,v in d.items()}
        mutant[key][index] = value
        try:
            check(mutant)
        except RuntimeError:
            rejected.append(key+str(index))
        else:
            raise RuntimeError('ineffective mutant')
    print(json.dumps({'status':'PASS','high_offsets':24,'low_offsets':24,'chain_sums':50,'rejected_mutants':rejected},sort_keys=True))

if __name__ == '__main__':
    main()
