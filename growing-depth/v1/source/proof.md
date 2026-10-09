# A growing prescribed-depth set from whole-arm cores

Internal research, 9 October 2026. No public release or worldwide novelty
claim. This construction changes the whole selected arm's auxiliary sequence,
including its turning region, and is outside the previously exhausted
invariant-preserving D-prefix trade. The path/spider statement below is
all-parameter; the saved finite checks support transcription only.

## 1. Exact statement and depth count

**Theorem.** Let s>=1 and r>=3s be integers, excluding r=3s+1. Put
k=2r+1. There is an explicit alpha-labeling of P_(2k+1) with designated
midpoint and threshold k-1, zero at depth 4s and maximum 2k at depth
4s+1 on one arm. Its two endpoint labels are (3k-1)/2 and (3k+1)/2.
Consequently, for every n>=2,m>=0 and every specified long-arm vertex
of S(k^n,1^m) at depth 4s or 4s+1, there is a graceful labeling
assigning that vertex zero.

The two zero placements are separate labelings, obtained by composition
and optional complementation. The path itself has one zero and one
maximum simultaneously, together with the required midpoint label.

For a fixed r the exact available index set supplied here is

    I_r = {s>=1 : 3s<=r and r!=3s+1}.

Equivalently, if r=3t, use s=1,...,t; if r=3t+1, use s=1,...,t-1;
if r=3t+2, use s=1,...,t. Empty ranges are omitted. In particular,
for every odd k>=11, all the distinct depths in

    {4s,4s+1 : 1<=s<=floor((k-5)/6)}

are covered for arbitrary n,m. This set has 2*floor((k-5)/6) elements
and grows without bound with k. At k=6t+1 the exact statement also
allows s=t, a pair beyond this convenient uniform lower bound.

This is partial prescribed-zero coverage. It does not establish full
zero-rotatability for any new infinite all-depth family, or resolve every
odd k and every depth. Depth classes congruent to 2 or 3 modulo 4,
and sufficiently distant interior depths, remain outside this construction.
Previously proved center, depths 1,2,k-1,k and short-leaf results can be
combined with it, but are not contributions of this theorem.

## 2. A graceful permutation of length 3s

Write p=3s. Form a permutation a of 0,...,p-1 by concatenating

    (1+3j, p-3-3j),  j=0,...,s-1,

and then the Walecki alternating order on the residue-2 entries

    p-1, 2, p-4, 5, p-7, 8, ...

(exactly s entries). More precisely its i-th tail entry, starting with
i=0, is 2+3(s-1-i/2) for even i, and 2+3((i-1)/2) for odd i.

The pairs contain every residue-1 value 1,4,...,p-2 and every
residue-0 value 0,3,...,p-3 once. The tail contains all residue-2
values once, so a is a complete permutation. It satisfies

    a_0=1,  a_(2s-1)=0,  a_(2s)=p-1.

Within the first 2s entries the consecutive differences are

    |p-4-3i|,  i=0,...,2s-2.

The signed progression starts at 3s-4 and ends at -3s+2; every
term is 2 modulo 3. Its positive terms are 2,5,...,p-4; the
absolute values of its negative terms are 1,4,...,p-2. Neither
progression repeats and they are disjoint. For s=1 the first
progression is empty and the second consists of 1, as required.
Thus these differences are exactly the nonmultiples of 3 in
[1,p-2]. The edge from the final zero of the pairs to the first
tail entry contributes p-1. The Walecki tail contributes

    3(s-1),3(s-2),...,3,

the positive multiples of 3 up to p-3. Together these partitions
give [1,p-1] exactly once. This proves that a is graceful.

The first examples are:

| s | p | a |
|---|---|---|
| 1 | 3 | 1,0,2 |
| 2 | 6 | 1,3,4,0,5,2 |
| 3 | 9 | 1,6,4,3,7,0,8,2,5 |
| 4 | 12 | 1,9,4,6,7,3,10,0,11,2,8,5 |

## 3. Symmetric alternating core and extension

Use side-tagged alternating objects H,L. Numeric values on opposite
sides may agree. Put

    y_i = a_i          if i is even,
    y_i = p-1-a_i      if i is odd,
    C = y followed by (p-1-y) in reverse order.

C has 2p entries, starts with H1 and ends with L(p-2). Its high
values are 0,...,p-1 once each: original even positions and reflected
odd positions contain the corresponding a_i. Its low values are
0,...,p-1 once each, using the corresponding complements of a_i.

For each edge of y, its sum and the reflected edge's sum are
p-1+d and p-1-d, where d is that edge's positive difference in a.
The central edge has sum p-1. Section 2 therefore proves that all
consecutive sums of C are exactly [0,2p-2]. This elementary
doubling is presented with proof, without claiming it as a new
alpha-path operation.

The entry a_(2s-1)=0 is at an odd original index and becomes high
offset zero at reflected index 2p-2s. The entry a_(2s)=p-1 is at
an even original index and becomes low zero at reflected index
2p-2s-1. With one-based positions in C these are, respectively,
4s+1 and 4s. Both are retained by the following extension.

### 3a. Four-entry extension

Suppose a balanced core uses [0,b-1] once on each side, has
consecutive sums [0,2b-2], and ends with L(b-2). Append

    H(b+1), L(b+1), H b, L b.

The incoming and three internal sums are

    2b-1, 2b+2, 2b+1, 2b.

They are exactly the next interval [2b-1,2b+2]. The enlarged core
uses [0,b+1] once on each side and ends with L b. Thus its size
parameter is b+2, and the same extension repeats.

If r-p is even, repeat this for b=p,p+2,...,r-2. Then append
the single high H(r+1). Its incoming sum, from L(r-2), is
2r-1. The complete sequence X has high set

    [0,r-1] union {r+1},

low set [0,r-1], first high 1, last high r+1, and consecutive
sums [0,2r-1] exactly once. When r=p no four-entry extension is
needed; the final single high still supplies 2r-1.

### 3b. Three-pair terminal patch for the opposite parity

If r-p is odd, the excluded r=p+1 is the only positive gap below
three. For all remaining cases r-p>=3. Repeat Section 3a's
four-entry extension only until b=r-3, and then append

    H(b+1), L b, H b, L(b+2), H(b+2), L(b+1), H(b+4).

Including the incoming edge from L(b-2), the new sums are

    2b-1, 2b+1, 2b, 2b+2, 2b+4, 2b+3, 2b+5.

They partition [2b-1,2b+5]=[2r-7,2r-1]. The additions supply
the low values b,b+1,b+2 and high values b,b+1,b+2,b+4;
b+3=r is absent from the high side, as required. Hence X has
exactly the same side sets, boundary entries and complete sum
partition as in Section 3a. No finite search premise enters either
extension proof.

The exclusion r=p+1 is a limitation of this formula. It is not a
nonexistence theorem for alpha paths or spider labelings. In
particular earlier public finite witnesses remain valid there.

## 4. Full midpoint alpha path

Interpret X as auxiliary offsets on the chosen left arm. At its
one-based depth i, use label 4r+2-X_(i-1) if i is odd, and
X_(i-1) if i is even. Give the midpoint label 2r. On the right
arm use

    R(2j+1)=2r+1+j,  j=0,...,r-1,
    R(2j)=2r-j,      j=1,...,r,
    R(2r+1)=3r+2.

The path, from endpoint to endpoint, is left in reverse order,
then midpoint, then right. Each arm has k=2r+1 entries. Its
midpoint is at path position k and has alpha value k-1.

**Vertex partition.** Left lows are [0,r-1]. Left highs are
{3r+1} union [3r+3,4r+2]. Right lows are [r,2r-1]; right highs
are [2r+1,3r] union {3r+2}. The midpoint 2r fills the only
remaining low label. These disjoint sets partition [0,4r+2]
exactly once. Every edge crosses threshold 2r, since depths
alternate high and low on both arms.

**Edge partition.** The right differences are 1,2,...,2r,2r+2.
The first left difference is (4r+1)-2r=2r+1. Every subsequent
left edge is a high-minus-low difference

    4r+2-(H+L).

By Section 3, its sums are [0,2r-1], giving all differences
[2r+3,4r+2] once. Thus all edges supply [1,4r+2]=[1,2k]
exactly once. This checks the full edge set, not just the new
core or its boundary edges.

Low zero remains at left depth 4s; high offset zero becomes
the actual maximum 4r+2=2k at left depth 4s+1. The endpoint
labels are 3r+1 and 3r+2, equivalent to the stated values in k.

Small cases make both parity routes explicit:

| s | r | k | Route | Zero/maximum depths |
|---|---|---|---|---|
| 1 | 3 | 7 | Bare p=3 core plus final high | 4,5 |
| 1 | 4 | 9 | Excluded by this formula | No assertion |
| 1 | 5 | 11 | One four-entry block | 4,5 |
| 1 | 6 | 13 | Three-pair patch | 4,5 |
| 2 | 6 | 13 | Bare p=6 core plus final high | 8,9 |
| 2 | 7 | 15 | Excluded by this formula | No assertion |
| 2 | 8 | 17 | One four-entry block | 8,9 |
| 2 | 9 | 19 | Three-pair patch | 8,9 |
| 3 | 9 | 19 | Bare p=9 core plus final high | 12,13 |

The bounded discovery solver reported INFEASIBLE for its exact
r=7,depth=8 whole-arm ansatz. The theorem needs no global
interpretation of that solver result, and none is made here.

## 5. Complete spider composition

This is the established alpha-amalgamation ingredient, not a new
operation. Write h=n-2,Q=hk+m. On the residual S(k^h,1^m),
label its center zero, and on arm i, 0<=i<h, use

    b(i,d)=(h-i)k-(d-1)/2    for odd d,
    b(i,d)=ik+d/2            for even d.

Label its short leaves hk+1,...,Q. Its even arm labels fill
[ik+1,ik+r] and its odd labels fill
[(h-i-1)k+r+1,(h-i)k]. Reversing the odd interval index
proves that all arm labels partition [1,hk]; the leaves give
[hk+1,Q]. The center label zero is distinct from all of them.

The center edges are the positive multiples of k through hk.
Internal arm differences are |(h-2i)k-u|, u=1,...,k-1. For
h-2i>=1 they fill the open k-block with index h-2i-1;
otherwise the block index is 2i-h. These two lists have opposite
parities and together partition 0,...,h-1, so the internal edges
give all the nonmultiples of k in [1,hk]. Short-leaf differences
complete [1,Q]. For h=0 the arm lists are empty; this also
includes Q=0 and the one-vertex residual tree.

Identify the residual center with the path midpoint. Add A=k-1
to every residual label b, keep all path labels <=A, and add Q
to every path label >A. The residual labels occupy [A,A+Q],
the low path labels occupy [0,A], and the high path labels
occupy [A+Q+1,2k+Q]. Their only overlap is label A at the
identified center. Thus the complete vertices bijectively use
[0,2k+Q]=[0,nk+m].

Residual edge differences stay [1,Q]; each alpha-path edge grows
by Q, so those differences are [Q+1,Q+2k]. Every edge difference
in [1,nk+m] occurs exactly once. The path's zero stays zero at
depth 4s; its maximum becomes nk+m at depth 4s+1. Complement
all labels about nk+m for the separate labeling with zero at
depth 4s+1. Permuting equal arms selects any specified arm.

## 6. Relation to the old trade and prior ingredients

The previous D-prefix class froze its side sets, its boundary
entries and its internal sum multiset, which forced a suffix
and restricted extreme depths to a constant set. Here s changes
the entire balanced core's side sets and length. Its symmetric
construction uses the turning region, and the odd terminal patch
also changes that region. At k=17 the depth-8/9 path alone
already lies outside the old class, whose exact extreme-depth
bound was at most 6/7. The old rigidity theorem is neither
contradicted nor used as a premise for this new construction.

The mathematical ingredients have material prior overlap:

- The alternating tail in Section 2 is the classical Walecki
  order. Its use and the general idea of turning graceful
  permutations into bipartite paths are not novelty claims.
- Symmetric doubling is proved directly here, but older path
  constructions may contain this exact transformation and the
  residue-3 permutation. Their historical provenance has not
  been established by this package.
- Patterson's 2017 thesis, Corollary 2.4.3 and Theorem 3.2.1,
  records the uniform center-zero and alpha-amalgamation
  ingredients. The latter is attributed to Huang-Kotzig-Rosa
  (1982). Rofa's rooted symmetric-tree formula also covers the
  residual center-zero construction. These are existing results.
- Earlier checked primary sources already cover all prescribed
  zeros for the degenerate cases n=2,m=0 and n=2,m=1. Those
  cases do not establish additional mathematical priority here.
- Cattell (2007), *Graceful labellings of paths*, concerns
  arbitrary specified vertices and labels, with alpha conditions;
  its scope is not restricted to endpoints. This package has
  not read the full paper or compared its machinery with the
  simultaneous midpoint, interior zero and adjacent maximum
  constraints. The doubling and core permutation might be
  subsumed by that or other older work. Worldwide novelty and
  non-subsumption remain unresolved.

These comparisons inherit the primary-source assessments in
../graceful-odd-editorial-2026-10-09/report.md and
../graceful-next-family/literature.md. No fresh source retrieval,
exhaustive literature search, or original-method assertion was
made in this mathematical package.

## 7. Evidence, release gate, and next missing identity

construct.py is formula-only. verify.py imports neither it nor
a solver, and reconstructs the core independently from residue
sets and symmetry before checking saved paths. It separately
builds every spider vertex and edge. It checks 156 saved paths,
960 complete spider labelings, and rejects two corruptions.
The largest saved parameters are s=1000,r=3003,k=6007.
Those are finite transcription checks. Sections 2-5 supply the
proof for unbounded s,r,n,m; no extrapolation from finite runs
is necessary.

The current package is author work with a separate checker
implementation, not an independent-agent mathematical audit,
external peer review, or proof-assistant verification. A separate
adversarial audit and major-result decision remain prerequisites
for any public use. Website, GitHub and public accounts were
not modified.

The bounded investigation ends at a concrete next identity:
construct additional balanced cores with endpoint H1,L(p-2),
each side [0,p-1], sums [0,2p-2], and low/high zero at the
missing depth pairs 4s+2,4s+3 or at depths approaching the
arm endpoint. The extension lemma then carries any such core
to every r>=p+2 and r=p. In the symmetric doubling route,
a sufficient identity is a graceful permutation starting at 1
whose adjacent 0,p-1 positions have the required parity and
reflected position 2p-j=4s+2, rather than this family's
2p-j=4s. No formula for those missing positions is claimed.
The remaining all-depth problem is open in this package.
