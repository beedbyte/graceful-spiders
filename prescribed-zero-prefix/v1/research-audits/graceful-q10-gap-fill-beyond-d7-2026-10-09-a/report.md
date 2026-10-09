# Private D8 extension of the accepted D7 prescribed-zero prefix

9 October 2026. Author mathematical construction, awaiting a separate internal
audit. Jordi Gartner owns and publishes this work through Beedbyte. AI assistance
in this package supported the residue construction, proof and fresh executable
graph checks. This is private evidence, without external review, formal proof-system
verification, publication or historical-priority determination. Existing records
and public content were preserved.

## Exact theorem proposed for acceptance

For every integer k>=19 define D8(k)=D7(k) when k<125. When k>=125, put

    p=floor((k-3)/2)=61+11a+r,     a>=0, 0<=r<=10,
    D8(k)=107+20a+2r.

For every n>=2,m>=0, any selected long arm of S(k^n,1^m), and every depth
2<=d<=D8(k), there is a graceful labeling with zero at that specified vertex.
Different requests may use different labelings. This includes both arm-length
parities and m=0.

The accepted D7 theorem supplies the starting prefix. This package supplies all
additional depths in six out of eleven p residue classes, without changing the
limiting ratio 10/11. Specifically, if F7(p) denotes the accepted endpoint and
F8(p)=107+20a+2r, then

    r:          0 1 2 3 4 5 6 7 8 9 10
    F8-F7:      0 2 0 2 0 2 0 2 0 2  4.

The first strict gain is k127 and k128: the prefix endpoint rises from107 to109.
At k145 and k146 it rises from123 to127. Each example repeats after adding22
to k and20 to both depth endpoints. These are previously unguaranteed depths
relative to D7, not claims that no earlier construction or literature covers them.

The theorem is a sufficient prefix. It does not assert full zero-rotatability,
optimality of D8, a slope above10/11 or novelty in the mathematical literature.

## Bound inherited premises

The D7 author report and its separate internal audit are bound in inputs.json:

- graceful-ten-elevenths-global-2026-10-09-a/report.md,
  SHA256 bf7eec616fa42a5465703e4f90d296f02dcb35a0b91c5c6c82bdfcf5208f9249.
- graceful-ten-elevenths-independent-2026-10-09-a/report.md.
- graceful-q10-q11-positive-independent-2026-10-09-a/report.md,
  SHA256 f90b3ef57a1f9d9f762f99a2db7b68eef8d88c1862e35809794122e54be33a44.

The precise seed literals are copied as seeds.json from the hash-bound earlier
reverse-complement data package. Only its size16 and size17 seeds are used here.
Their reflected maximum-pair first depths are both26. Their compatible core
contracts and the generic odd/even shells are inherited from the accepted
packages, and checked again as literal partitions below. RESTART.md was read
as context; its observed hash is in context.json rather than a proof premise,
since the root chat may update that checkpoint.

The earlier author Python source was read while orienting this work. Therefore
this package does not claim a blind or separate independent audit. check.py is
a fresh author implementation, imports no predecessor module and implements
insertion by tagged graph edge replacement and path traversal. Separate audit
of this exact new theorem remains necessary before treating it as accepted.

## Universal construction

A compatible core of size p is an alternating H,L path with2p vertices, each
tag side permuting0..p-1, adjacent sums permuting0..2p-2, endpoints H3,L(p-4),
and the window H4,L0,H0,L1. Our seeds additionally have the adjacent maximum
pair p-1,p-1 entirely before that window.

Use the following P2 gadgets, with P starting H and B,D starting L:

    q9:
      P=[3,6]
      B=[9,4]
      D=[1,1,2,5,3,2,4,6,5,7,7,8,8,9]
    q10:
      P=[3,8]
      B=[10,8,9,10,5,5,4,2,3,4]
      D=[1,1,2,6,6,7,7,9]
    q11:
      P=[3,8]
      B=[11,10,5,5,4,2,3,4]
      D=[1,1,2,6,6,7,7,9,10,8,9,11].

Every block has positive even length. For each literal the combined fresh
H offsets and combined fresh L offsets each permute1..q. The three chains

    P,H(q+3);    H(q+4),B,L0;    H0,D,L(q+1)

have sums[1,2q+1] union{2q+4}, once each. These are finite integer identities
checked directly by check.py and already supported by the accepted predecessors.

To insert, shift every old positive offset by q and keep the old zeros. Delete
the two old window boundary edges. Attach P before the shifted old first vertex;
use B and D to reconnect the respective window boundaries. Retained edge sums
are{0} union([2q+2,2p+2q-2] minus{2q+4}); fresh chains supply the complementary
sums. The combined sides become0..p+q-1. The endpoints become H3,L(p+q-4),
and B ending at H4 and D starting at L1 preserve the window. Thus the operation
is valid for every compatible input and can be iterated in any finite word.

The old adjacent maximum pair remains unique, becomes p+q-1,p+q-1, and stays
before the window. Its first zero-based index t increases by len(P)=2. At the
end of all insertions, apply

    T_p(C)[i]=p-1-C[2p-1-i].

This reverse-complement preserves the shell contract: tags swap, side ranges
are complemented, sums become2p-2-s, and endpoints remain H3,L(p-4). The old
maximum pair becomes a zero pair at one-based depths2p-1-t and2p-t. Consequently
a q insertion before the final reflection increases the two reflected depths
by2q-2:16,18,20 for q9,q10,q11. This proves the depth arithmetic for arbitrary
iteration, rather than extrapolating finite runs. Reflection is performed once,
after all insertions; no compatibility of a reflected core is assumed.

For a seed size s in{16,17}, counts(c,b,a) of q9,q10,q11 produce

    p=s+9c+10b+11a,
    depths={26+16c+18b+20a, 27+16c+18b+20a}.

## Seven finite recipes and the unbounded gap proof

The literal recipes.json records the following table. All rows are valid
compatible-core recipes under the universal construction above.

| p | Seed size | q9 count | q10 count | q11 count | Resulting depths |
|---|---:|---:|---:|---:|---|
|62|16|4|1|0|108,109|
|64|16|3|1|1|112,113|
|66|16|2|1|2|116,117|
|68|16|1|1|3|120,121|
|70|16|0|1|4|124,125|
|71|17|0|1|4|124,125|
|71|16|0|0|5|126,127|

At p61,63,65,67,69, F8=F7, so no additional construction is needed. At
p62,64,66,68,70, the corresponding row is precisely[F7+1,F8]. At p71,
F7=123 and F8=127: the size17 row supplies124/125 and the size16 row126/127.
The latter pair alone would leave a gap; no such single-pair inference is used.

For arbitrary p>=61 write p=p0+11a with p0 in61..71. Both F7 and F8 satisfy
F(p0+11a)=F(p0)+20a, by their definitions. In every row for p0 add a q11
insertions BEFORE final reflection. The universal construction increases size
by11a and both depths by20a. Therefore the translated finite rows cover exactly
every missing integer in[F7(p)+1,F8(p)] for all p>=61. The already accepted
D7 theorem supplies2..F7(p). Their union is the required full prefix.

This argument adds q11 operations to recipes, not to an arbitrary already
reflected core or an abstract full-spider labeling. It requires no C6 append,
no new induction over an inherited core interval, and no search completeness.

For additional arithmetic intuition, let y=p-16 and t=ceil(y/11). For p>=61,
y>=45 and9t<=y<=11t. Thus some t gadgets of sizes9,10,11 have total size y.
Using only seed16 and P2 gadgets their upper depth is

    27+2y-2t=2p-5-2ceil((p-16)/11)=F8(p).

This explains the endpoint formula, but by itself proves only the top pair.
The seven-row gap argument is what proves the contiguous prefix, especially
at residue r10. No exactness or optimality claim for the expanded recipe family
is made.

## Actual-spider transport, including parity and zero orientation

Let a reflected constructed core have size p. It retains exactly the shell
contract; no window condition or fixed orientation of its zero pair is needed.
For odd k=2p+3 set M=2k,A=2p+2. Map Hx to M-x and Lx to x along the selected
arm, followed by(3p+3,p+1,3p+4). The partner arm has pairs
(2p+3+i,2p+1-i), i=0..p-1, followed by(3p+6,p,3p+5).

For even k=2p+4 set M=2k,A=2p+4. Use the same core map, selected tail
(3p+5,p+2,3p+7,p+3), partner pairs(2p+5+i,2p+3-i), and partner tail
(3p+6,p,3p+8,p+1). The accepted shell partitions give labels0..M, weights1..M,
and every edge crosses A. These formulas appear explicitly in check.py and
are verified on every constructed instance in both parities.

For n>=2 choose the selected arm and any distinct partner. Put h=n-2,Q=hk+m,
N=nk+m. The residual spider has center0, its arm i at odd depth2u+1 labeled
(h-i)k-u, at even depth2u labeled ik+u, and short leaves hk+1..Q. Its labels
and weights are0..Q and1..Q. The block partitions proving this work for both
parities, all h,m, including h=m=0. Shift residual noncenter labels by A,
identify its center with shell center A, and shift shell labels>A by Q.
Then residual weights remain1..Q and all shell weights increase by Q, yielding
Q+1..N; the labels partition0..N. Thus the result is graceful on exactly the
named spider S(k^n,1^m).

The L0 core member carries0, and the H0 member carriesN. Complement the ENTIRE
graph by N-x when targeting the latter. Hence both consecutive depths in every
row work, and the named selected arm may be arbitrary. Tails are appended so
the one-based core depths equal actual center distances. Since
p=floor((k-3)/2), the same p applies to k=2p+3 and k=2p+4, establishing every
integer k with no skipped parity. All finite recipe gains therefore lift to
the full n,m,arm quantifiers rather than only a two-arm path.

## Bounds, joins and quantitative comparison

Direct subtraction gives F8-F7=2r-4floor(min(r,9)/2), which is the eleven-entry
gain table above, including value4 at r10. It is independent of a and of the
arm-length parity. Inside a block F8 grows by2 per increase of p; at r10 to the
next r0 it stays constant. It is thus nondecreasing. At p61 the value107 equals
D7; D7 was already monotone across the low/high join. D8>=D7 at all k>=19.

Writing k=2p+3+epsilon with epsilon in{0,1}, substitution yields

    10k-11D8(k)=73-2r+10epsilon      (k>=125).

Across eleven residues and both parities the exact tail range is53..83.
This improves the D7 high-branch deficit range57..107, though minima occur in
different residues. The inherited k19..124 branch still has maximal deficit261
at k124. Therefore globally0<=10k-11D8(k)<=261, all asserted depths are legal,
and D8(k)/k tends to10/11 through all integers. The extension adds bounded
numbers of depths on infinitely many lengths; it does not improve this limit.

## Executable checks, negative tests, and frozen evidence

Run with standard Python, no solver or third-party package:

    python -B check.py
    python -B -O check.py

The checker verifies historical input hashes before and after execution,
the exact copied seeds, every fresh gadget side/sum partition, the finite
residue coverage, and all seven recipes with extra q11 counts0,1,2,7,19.
For every resulting core it builds actual spiders in both parities with
(n,m)=(2,0),(3,0),(3,2),(5,7), selected arms0,n-1 and both target depths.
Graph adjacency is created separately from the labels. Full label/edge
permutations and BFS test the graph and prescribed vertex. The main matrix
contains1120 spiders; two additional diagnostic instances give1122 total.
The run checks827 core contracts and393 graph insertions.

Thirteen negative controls reject a corrupted prefix for each gadget, a
wrong recipe size, wrong reflected gain, premature reflection, the incomplete
r10 single-pair argument, and duplicated target labels, incorrect BFS depth,
and partial complementation in each shell parity. Checks use explicit
exceptions and survive optimized Python. Normal and optimized result files
match byte for byte. The formula sweep p61..100000 is supplementary evidence;
the unbounded proof consists of the finite identities and universal translation
argument above.

The author inspected source material and wrote this checker in the same task;
these results are not a separate mathematical audit. No external review or
Lean formalization is asserted. manifest.json binds this proof, checker, literal
recipes/seeds, source bindings, context hash and both result files. No existing
historical evidence, common checkpoint or public source was modified.
