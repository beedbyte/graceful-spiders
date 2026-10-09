"""Independent formula audit; never imports or executes the submitted Python files.

Run: python independent_check.py [source-directory]
All comparisons raise explicit exceptions, so verification also works under -O.
"""
from collections import deque
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
SOURCE = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else HERE.parent / 'graceful-whole-arm-next-2026-10-09'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def interval(values, first, last, context):
    require(sorted(values) == list(range(first, last + 1)), context)


def differences(values):
    return [abs(y - x) for x, y in zip(values, values[1:])]


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def manifest():
    found = {}
    for line in (SOURCE / 'SHA256SUMS.txt').read_text().splitlines():
        expected, name = line.split(maxsplit=1)
        file = SOURCE / name
        require(file.parent == SOURCE, 'manifest path outside frozen directory')
        observed = sha256(file.read_bytes()).hexdigest()
        require(observed == expected, 'source SHA256 mismatch: ' + name)
        found[name] = observed
    require(len(found) == 8, 'unexpected manifest size')
    return found


def core(s):
    require(type(s) is int and s >= 1, 's outside theorem domain')
    p = 3*s
    # Assemble the residue classes directly, then consume the residue-2 deque.
    a = [v for pair in zip(range(1, p, 3), range(p-3, -1, -3)) for v in pair]
    tail = deque(range(2, p, 3))
    high_end = True
    while tail:
        a.append(tail.pop() if high_end else tail.popleft())
        high_end = not high_end
    interval(a, 0, p-1, 'permutation')
    require(a[0] == 1 and a[2*s-1] == 0 and a[2*s] == p-1, 'permutation anchors')
    require(sorted(differences(a[:2*s])) == [x for x in range(1,p-1) if x % 3], 'nonmultiple differences')
    require(a[2*s] - a[2*s-1] == p-1, 'bridge difference')
    require(differences(a[2*s:]) == list(range(3*(s-1),0,-3)), 'tail differences')
    interval(differences(a), 1, p-1, 'graceful permutation')
    # Direct reflected-index evaluation instead of appending reversed y.
    c = []
    for j in range(2*p):
        i = j if j < p else 2*p-1-j
        y = a[i] if i % 2 == 0 else p-1-a[i]
        c.append(y if j < p else p-1-y)
    interval(c[::2], 0, p-1, 'balanced high offsets')
    interval(c[1::2], 0, p-1, 'balanced low offsets')
    interval([x+y for x,y in zip(c,c[1:])], 0, 2*p-2, 'core sum partition')
    require(c[0] == 1 and c[-1] == p-2, 'core boundaries')
    require(c[4*s-1] == c[4*s] == 0, 'tagged adjacent core zeros')
    return c


def path(s, r):
    require(type(r) is int and r >= 3*s and r != 3*s+1, 'r outside theorem domain')
    x = core(s)
    p = 3*s
    terminal = r if (r-p) % 2 == 0 else r-3
    for b in range(p, terminal, 2):
        segment = [b+1, b+1, b, b]
        interval([x[-1]+segment[0]] + [u+v for u,v in zip(segment,segment[1:])], 2*b-1, 2*b+2, 'four-entry increment')
        x.extend(segment)
    if terminal == r:
        require(x[-1] + r+1 == 2*r-1, 'even terminal incoming sum')
        x.append(r+1)
    else:
        b = r-3
        segment = [b+1, b, b, b+2, b+2, b+1, b+4]
        interval([x[-1]+segment[0]] + [u+v for u,v in zip(segment,segment[1:])], 2*r-7, 2*r-1, 'odd terminal increment')
        x.extend(segment)
    require(sorted(x[::2]) == list(range(r))+[r+1], 'extended high set')
    interval(x[1::2], 0, r-1, 'extended low set')
    interval([u+v for u,v in zip(x,x[1:])], 0, 2*r-1, 'extended sum partition')
    require(x[0] == 1 and x[-1] == r+1, 'extended boundaries')
    k, q = 2*r+1, 4*r+2
    left = [q-v if j % 2 == 0 else v for j,v in enumerate(x)]
    right = []
    for depth in range(1,k+1):
        right.append(3*r+2 if depth == k else (2*r+(depth+1)//2 if depth % 2 else 2*r-depth//2))
    require(sorted(left[::2]) == [3*r+1] + list(range(3*r+3,4*r+3)), 'left high partition')
    interval(left[1::2], 0, r-1, 'left low partition')
    require(sorted(right[::2]) == list(range(2*r+1,3*r+1))+[3*r+2], 'right high partition')
    interval(right[1::2], r, 2*r-1, 'right low partition')
    require(sorted(differences([2*r]+right)) == list(range(1,2*r+1))+[2*r+2], 'right edge partition')
    require(abs(left[0]-2*r) == 2*r+1, 'left center edge')
    interval(differences(left), 2*r+3, 4*r+2, 'left internal edges')
    result = left[::-1]+[2*r]+right
    validate_path(result,s,r)
    return result


def validate_path(a,s,r):
    k = 2*r+1
    interval(a,0,2*k,'path vertex bijection')
    interval(differences(a),1,2*k,'path edge bijection')
    require(a[k] == k-1,'midpoint label')
    require(all((u <= k-1) != (v <= k-1) for u,v in zip(a,a[1:])), 'alpha threshold')
    require(a[k-4*s] == 0 and a[k-4*s-1] == 2*k, 'prescribed extreme depths')
    require((a[0],a[-1]) == (3*r+1,3*r+2), 'endpoint labels')


def spider(s,r,n,m,arm,depth):
    require(n >= 2 and m >= 0 and 0 <= arm < n and depth in (4*s,4*s+1), 'spider parameter domain')
    k = 2*r+1
    a = path(s,r)
    q = (n-2)*k+m
    threshold = k-1
    other = min(set(range(n))-{arm})
    remaining = [j for j in range(n) if j not in (arm,other)]
    labels = {'c':threshold}
    for j,direction in ((arm,-1),(other,1)):
        for d in range(1,k+1):
            z = a[k+direction*d]
            labels[f'a{j}:{d}'] = z + (q if z > threshold else 0)
    residual = [0]
    residual_edges = []
    for i,j in enumerate(remaining):
        previous = 0
        for d in range(1,k+1):
            b = (n-2-i)*k-d//2 if d % 2 else i*k+d//2
            residual.append(b)
            residual_edges.append(abs(previous-b))
            previous = b
            labels[f'a{j}:{d}'] = threshold+b
    for i in range(m):
        b = (n-2)*k+i+1
        residual.append(b)
        residual_edges.append(b)
        labels[f'l{i}'] = threshold+b
    interval(residual,0,q,'residual label partition')
    interval(residual_edges,1,q,'residual edge partition')
    require(labels[f'a{arm}:{4*s}'] == 0 and labels[f'a{arm}:{4*s+1}'] == n*k+m,'precomplement extrema')
    if depth == 4*s+1:
        labels = {v:n*k+m-z for v,z in labels.items()}
    validate_spider(labels,k,n,m,arm,depth)
    return labels


def validate_spider(labels,k,n,m,arm,depth):
    # Enumerate the graph from the parameters, independently of its labeling.
    edges = []
    vertices = {'c'}
    for i in range(n):
        previous = 'c'
        for d in range(1,k+1):
            v = f'a{i}:{d}'
            vertices.add(v)
            edges.append((previous,v))
            previous = v
    for i in range(m):
        v = f'l{i}'
        vertices.add(v)
        edges.append(('c',v))
    require(set(labels) == vertices, 'spider vertex identities')
    interval(labels.values(),0,n*k+m,'spider vertex bijection')
    interval([abs(labels[u]-labels[v]) for u,v in edges],1,n*k+m,'spider edge bijection')
    require(labels[f'a{arm}:{depth}'] == 0,'specified spider zero')


def main():
    pinned = manifest()
    data = json.loads((SOURCE / 'certificates.json').read_text())
    records = {'paths':[], 'spiders':[]}
    rebuilt = {'paths':[], 'spiders':[]}
    for record in data['paths']:
        s,r = record['s'],record['r']
        validate_path(record['path'],s,r)
        expected = path(s,r)
        require(record['path'] == expected, f'path formula mismatch {s,r}')
        reconstructed = {'s':s,'r':r,'path':expected}
        rebuilt['paths'].append(reconstructed)
        records['paths'].append({'s':s,'r':r,'saved_sha256':digest(record),'reconstructed_sha256':digest(reconstructed)})
    for record in data['spiders']:
        args = [record[key] for key in ('s','r','n','m','arm','depth')]
        s,r,n,m,arm,depth = args
        validate_spider(record['labels'],2*r+1,n,m,arm,depth)
        expected = spider(*args)
        require(record['labels'] == expected, f'spider formula mismatch {args}')
        reconstructed = dict(zip(('s','r','n','m','arm','depth'),args),labels=expected)
        rebuilt['spiders'].append(reconstructed)
        records['spiders'].append(dict(zip(('s','r','n','m','arm','depth'),args),saved_sha256=digest(record),reconstructed_sha256=digest(reconstructed)))
    require(digest(data) == digest(rebuilt), 'aggregate certificate digest')
    count_paths = 0
    # All admissible pairs in a rectangle, then unbounded-parameter stress samples.
    for s in range(1,61):
        for r in range(3*s,221):
            if r != 3*s+1:
                path(s,r)
                count_paths += 1
    stress = [(s,3*s+gap) for s in (100,1000,10000) for gap in (0,2,3,4,5,20,21)]
    for s,r in stress:
        path(s,r)
    count_spiders = 0
    for s in range(1,5):
        for gap in (0,2,3,4,5):
            r = 3*s+gap
            for n in range(2,10):
                for m in (0,1,2,7):
                    for arm in range(n):
                        for depth in (4*s,4*s+1):
                            spider(s,r,n,m,arm,depth)
                            count_spiders += 1
    spider_stress = [(1,3,100,100,99,4), (2,8,101,0,50,9), (10,33,31,61,17,40), (100,303,12,1000,11,401)]
    for args in spider_stress:
        spider(*args)
    for r in range(1,3001):
        exact = [s for s in range(1,r//3+1) if r != 3*s+1]
        count = r//3-(1 if r % 3 == 1 and r>=4 else 0)
        require(len(exact) == count, 'exact index count')
        if r >= 5:
            guaranteed = list(range(1,(r-2)//3+1))
            require(set(guaranteed) <= set(exact), 'lower-bound index inclusion')
            depths = [d for s in guaranteed for d in (4*s,4*s+1)]
            require(len(set(depths)) == 2*((2*r+1-5)//6), 'lower-bound distinct-depth count')
            require(all(d <= 2*r+1 for d in depths), 'depth within arm')
    rejected = []
    def reject(name, test):
        try:
            test()
        except ValueError as error:
            rejected.append({'name':name,'rejection':str(error)})
            return
        raise ValueError('negative control accepted: '+name)
    a = path(1,3)
    duplicate = a.copy()
    duplicate[0] = duplicate[1]
    reject('duplicate path label',lambda:validate_path(duplicate,1,3))
    swapped = a.copy()
    swapped[0],swapped[1] = swapped[1],swapped[0]
    reject('permutation-preserving edge corruption',lambda:validate_path(swapped,1,3))
    reject('graceful reversed path has wrong prescribed side',lambda:validate_path(a[::-1],1,3))
    reject('graceful complemented path has wrong midpoint',lambda:validate_path([14-z for z in a],1,3))
    labels = spider(1,3,3,2,2,4)
    corrupt = deepcopy(labels)
    corrupt['l0'],corrupt['a2:4'] = corrupt['a2:4'],corrupt['l0']
    reject('spider permutation-preserving corruption',lambda:validate_spider(corrupt,7,3,2,2,4))
    missing = deepcopy(labels)
    missing.pop('l0')
    reject('missing spider vertex',lambda:validate_spider(missing,7,3,2,2,4))
    reject('valid spider wrong requested zero depth',lambda:validate_spider(labels,7,3,2,2,5))
    for s,r in ((0,3),(1,2),(1,4),(2,7),(100,301)):
        reject(f'excluded domain s={s},r={r}',lambda s=s,r=r:path(s,r))
    # Omitting the parity patch cannot silently pass: append only final high
    # to the p=3 core and interpret it as r=4, which must fail the path size.
    invalid_x = core(1)+[5]
    bad_left = [18-z if j%2 == 0 else z for j,z in enumerate(invalid_x)]
    bad_right = [9,7,10,6,11,5,12,4,14]
    reject('excluded r=p+1 naive continuation',lambda:validate_path(bad_left[::-1]+[8]+bad_right,1,4))
    require(manifest() == pinned,'source changed during audit')
    result = {
        'verdict':'PASS',
        'independent_agent_audit':True,
        'method':'proof.md formulas only; no reading/import/execution of submitted construct.py or verify.py',
        'manifest_files_verified':pinned,
        'manifest_sha256':sha256((SOURCE/'SHA256SUMS.txt').read_bytes()).hexdigest(),
        'saved_paths':len(data['paths']),
        'saved_spiders':len(data['spiders']),
        'saved_certificate_file_sha256':pinned['certificates.json'],
        'saved_canonical_certificate_sha256':digest(data),
        'independently_reconstructed_canonical_certificate_sha256':digest(rebuilt),
        'extra_path_rectangle':{'s':[1,60],'r':[3,220],'admissible_pairs_checked':count_paths},
        'extra_path_stress_parameters':stress,
        'extra_spider_grid':{'s':[1,4],'r_minus_3s':[0,2,3,4,5],'n':[2,9],'m':[0,1,2,7],'arms':'every arm','depths':'both','cases':count_spiders},
        'extra_spider_stress_parameters':spider_stress,
        'exact_index_and_lower_bound_r_range':[1,3000],
        'negative_controls_rejected':rejected,
        'counterexample_found':None,
        'smallest_excluded_parameters':{'s':1,'r':4,'k':9,'note':'formula exclusion, not a graph nonexistence result'},
        'all_parameter_proof':'See audit-report.md; finite checks are transcription evidence only.',
    }
    (HERE/'certificate-hash-comparison.json').write_text(json.dumps(records,indent=2)+'\n')
    (HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ('verdict','saved_paths','saved_spiders','extra_path_rectangle','extra_spider_grid','saved_canonical_certificate_sha256','independently_reconstructed_canonical_certificate_sha256')},indent=2))
    print('Negative controls rejected:',len(rejected))


if __name__ == '__main__':
    main()
