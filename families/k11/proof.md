# Certified k=11 extension

Certificate extension, 9 October 2026. The all-parameter argument and all four certificates passed a separate agent audit; publication priority is unresolved. No external expert review or formal proof verification is claimed.

**Result:** For all integers n>=2 and m>=0, the tree S(11^n,1^m)
is zero-rotatable. Here the center has n arms of 11 edges and m further leaves.
The n=2,m=0 boundary is a path with its distinguished center. This is a
complete k=11 family extension of the argument in
`../proof.md`, not a conjectural extrapolation.

## Exact certificates

Each row is a path on positions 0,...,22. Its midpoint position 11 has label
10, its alpha threshold. The low side is labels 0,...,10 and the high side
is 11,...,22. Every edge crosses these sides.

| Zero depth | Maximum depth | Labels from one endpoint to the other | Search DFS entries |
|---:|---:|---|---:|
| 2 | 3 | (18,4,19,3,20,2,21,1,22,0,13,10,11,9,14,7,16,8,12,6,17,5,15) | 41,618,132 |
| 4 | 5 | (19,3,20,2,21,1,22,0,15,6,16,10,11,9,12,8,13,5,17,4,18,7,14) | 46,260,068 |
| 6 | 7 | (20,2,21,1,22,0,17,3,19,4,14,10,11,9,12,6,18,5,16,7,15,8,13) | 81,409,148 |
| 8 | 9 | (21,1,22,0,19,2,20,4,16,7,13,10,11,9,14,6,17,3,18,5,15,8,12) | 122,602,452 |

Each row is a permutation of 0,...,22, and the differences between consecutive
entries are a permutation of 1,...,22. `check.py` checks these statements
directly, without importing the search, original construction, or original
checker. Thus the search itself need not be trusted to certify existence.

## Why the finite paths prove an unbounded family

Use the center-zero labeling b of G=S(11^(n-2),1^m) proved in Section 1
of the preceding proof. Its number of edges is Q=11(n-2)+m. Identify its
center with the midpoint of any certified path a. On G set f=b+10; on the
path keep low labels fixed and add Q to every high label.

The labels of G are [10,10+Q], the path low labels [0,10], and the high
labels [11+Q,22+Q]. Only the shared center repeats before identification,
so the combined labels are exactly 0,...,11n+m. Differences inside G are
1,...,Q. Each path difference increases by Q because every path edge crosses
the threshold, so these differences are Q+1,...,Q+22. The combined labeling
is graceful. Its path zero stays zero and its path maximum becomes 11n+m.
Complementing all labels makes that latter vertex zero. Arm permutations
place each zero depth on any selected arm.

The four certificates therefore cover depths 2,3,4,5,6,7,8,9, for every
n>=2,m>=0. Sections 3 and 4 of the preceding proof cover depths 1,2,10,11,
the center, and every short leaf. These exhaust all vertices, proving the
stated k=11 result. The cited sections contain algebraic constructions and
proofs for all parameters, so this conclusion does not rely on a finite
test grid of spiders.

## Reproduction and bounded-search status

```
python check.py
node search.js 11 2 zero 500000000 -1
node search.js 11 4 zero 500000000 -1
node search.js 11 6 zero 500000000 -1
node search.js 11 8 zero 500000000 -1
```

The search is a copy of the prior `path_probe.js` with its success status
renamed FOUND. It fixes midpoint label 10, zero at position 11-d, maximum
22 at position 10-d, and alpha side by parity relative to the midpoint.
It enumerates unused labels of that side at the most constrained frontier
position, rejecting reused differences. The bit masks are valid for q=22;
this implementation is not a general large-k solver.

All four 500,000,000-entry runs returned FOUND, as recorded above and in
`certificates.json`. Earlier runs with 20,000,000-entry budgets returned
UNKNOWN at entry 20,000,001. No run returned EXHAUSTED. An EXHAUSTED result
would concern only the explicit midpoint, extremum-position and bipartition
constraints above. UNKNOWN means the budget did not decide existence and
must never be interpreted as impossibility.

The independent checker passed four exact certificates and 1,680 composed
labelings with zero checked at an exact arm vertex, using n=2,3,4,5,8,20
and m=0,1,2,5,30, both extremes of each certificate, and every arm. It also
rejected two deliberately corrupted inputs. These are transcription checks;
the proof above supplies the unbounded statement. Formal proof-assistant
verification and independent external mathematical review remain absent.

The composition and center/leaf operations are known ingredients documented
in `../literature.md`; this task required no new
literature-dependent lemma. No claim of publication priority, originality,
or coverage for arbitrary odd k follows. The general odd-k question remains
unresolved here; the specific k=11 family is now certified by exact paths
and the established composition argument.
