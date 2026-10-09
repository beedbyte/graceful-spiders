# Separate internal mathematical audit: D8 gap completion

Private record, 9 October 2026. **GO for the exact D8 theorem in the frozen
author report bound below.** The seven finite recipes, universal insertions,
unbounded q11 translation, complete interval joins, actual-spider transfer and
quantitative claims have been reconstructed separately. No counterexample or
mathematical defect was found. This is internal checking, not external review,
peer review, a Lean proof or historical-priority verification. Jordi Gartner
owns and publishes this work through Beedbyte. AI assistance supported this
proof reconstruction and the separate executable checks. No shared checkpoint,
historical artifact or public content was changed.

## Exact accepted theorem

For every integer k>=19, use the accepted D7(k) when k<125. For k>=125 put
p=floor((k-3)/2)=61+11a+r, with a>=0 and0<=r<=10, and define

    D8(k)=F8(p)=107+20a+2r.

For all n>=2,m>=0, every selected long arm of S(k^n,1^m), and each integer
2<=d<=D8(k), a graceful labeling exists with zero at that exact depth-d
vertex. Different requests may use different labelings. The statement includes
both k parities and n2,m0. D8>=D7, the global deficit satisfies
0<=10k-11D8(k)<=261, and D8(k)/k tends to10/11 through all integers.
The gain is bounded but occurs at infinitely many lengths; the limiting
fraction is unchanged. No full zero-rotatability or optimality follows.

## Source binding and independence

Author directory: graceful-q10-gap-fill-beyond-d7-2026-10-09-a.
The requested hashes were checked BEFORE reading the report or data:

| Artifact | SHA-256 |
|---|---|
| report.md | `3150df1b1f6296c580eebf5c2bc4b7bba9b6ae97436b0ebfbb821f70c41658a6` |
| check.py | `34935d2f44e14eaaaecf992fc5b94e2cfdcee2df8133390d555037cd91bff54e` |
| manifest.json | `ce41485e485b6dd86c92092923326fdaa47095fa8243eb4d733c4531d5d5b685` |

The author Python was never read, executed or imported. The new audit.py checks
all eight author manifest payloads and every historical input binding before
and after its run. recipes.json and seeds.json are treated as finite integer
certificates. The copied seed literals are also compared with the older accepted
48-seed bank. AGENTS.md and EDITORIAL_POLICY.md were followed; mutable RESTART
is context rather than an immutable mathematical premise.

core_graph.py is an exact copy of this auditor's earlier frozen independent
implementation, predating the D8 author package. Its provenance is bound in
source-inputs.json; it is not represented as a newly independent implementation
of those inherited parts. It uses tagged graph edge deletion/subdivision,
degree/connectivity checks and traversal. The new D8 recipe checker, mixed-word
tracking, interval validation and negative controls call this own code only.
Actual named spider adjacency is built separately from labels and checked by BFS.
All code uses only Python's standard library and explicit exceptions.

The inherited D7 audit report is
`60a958449111a6f875be84a05d419c94c474db0cb770b3c07af799f57633c1cf`,
and the q10/q11 universal-gadget audit report is
`f90b3ef57a1f9d9f762f99a2db7b68eef8d88c1862e35809794122e54be33a44`.
Those accepted results are explicit premises, not conclusions inferred anew
from the bounded D8 matrix.

## Universal insertion and tracked-depth reconstruction

A compatible core has length2p, starts H and alternates H,L, each tag side
permuting0..p-1, all consecutive sums permuting0..2p-2, endpoints H3,L(p-4),
and window H4,L0,H0,L1. The two selected seeds are the earlier bank entries
(p,old-zero-depth)=(16,16),(17,22). Their maximum pairs occur at one-based
positions6/7 and8/9 respectively, both before the zero window. Their reflected
pair depths are26/27 in each case.

The literal q9, q10 and q11 gadgets have P length2, positive entries, even
nonempty P/B/D lengths, P starting H3, B ending H4 and D starting L1. P is
tagged H,L,... and B,D are tagged L,H,... . Direct integer arithmetic verifies
that the new H and L offsets each permute1..q and the three replacement
chains P,H(q+3); H(q+4),B,L0; H0,D,L(q+1) have sums

    [1,2q+1] union {2q+4}, exactly once.

In particular q10 has P=[3,8], B=[10,8,9,10,5,5,4,2,3,4] and
D=[1,1,2,6,6,7,7,9]; its chain sums are1..21 and24. The q11 literal has
P=[3,8], B=[11,10,5,5,4,2,3,4] and D=[1,1,2,6,6,7,7,9,10,8,9,11];
its chain sums are1..23 and26. q9 is the accepted P=[3,6],B=[9,4] gadget
whose D is[1,1,2,5,3,2,4,6,5,7,7,8,8,9].

Shift every old positive offset by q, keep both zeros, and replace the two
old window boundary edges. The retained zero-zero sum is0; the removed sums
were1 and4; every other retained sum increases by2q. Thus retained sums are
{0} union ([2q+2,2p+2q-2] minus{2q+4}). The three chains fill their exact
complement. Fresh offsets1..q, shifted old positives q+1..p+q-1 and the
retained zero fill each tag side. The even block lengths preserve alternation;
the endpoints and four-entry window persist. This proves an insertion for
every compatible input, independent of any search status.

All selected old maximum offsets are positive and become p+q-1, greater than
every fresh offset because p>=16. The maximum pair's edge is untouched and
remains before the zero window. Only P precedes it, so its first index advances
by2. This invariant persists for every finite mixed word of the three gadgets.

At the end apply T(C)[i]=p-1-C[2p-1-i]. Reversal swaps source tag parity;
complementation permutes each tag range. Consecutive sums map to2p-2-s,
and endpoints map to3 and p-4. The shell contract is therefore preserved,
even though the insertion window need not survive. If the old maximum pair
starts at zero-based index t, the reflected zeros occur at depths2p-1-t and
2p-t. A q insertion advances each reflected depth by2q-2, namely16,18,20.
Every insertion occurs before the one final reflection.

Consequently seed size s16/17 and counts(c,b,a) of q9,q10,q11 give exactly

    p=s+9c+10b+11a,
    zero-offset depths=26+16c+18b+20a and27+16c+18b+20a.

The theorem uses both members, with full-spider complement for the high one.

## Seven recipes and every missing depth

Direct application of these identities verifies all seven literal rows:

| Size p | Seed | (q9,q10,q11) counts | Depths |
|---|---:|---|---|
|62|16|(4,1,0)|108,109|
|64|16|(3,1,1)|112,113|
|66|16|(2,1,2)|116,117|
|68|16|(1,1,3)|120,121|
|70|16|(0,1,4)|124,125|
|71|17|(0,1,4)|124,125|
|71|16|(0,0,5)|126,127|

The accepted endpoint is F7(p)=107+20a+4floor(min(r,9)/2), so subtracting
it from F8 gives, for residues r0..10,

    [0,2,0,2,0,2,0,2,0,2,4].

At base sizes61,63,65,67,69 there is no gap. The rows for62,64,66,68,70
give exactly the five missing two-depth intervals. At71 the two rows jointly
give the four-depth interval124..127. The high pair126/127 alone leaves
124/125 missing. Both false single-pair replacements are rejected by controls.

For any p>=61 choose its unique p0 in61..71 with p=p0+11t,t>=0. Both
endpoint functions increase by20t, and adding t q11 moves to a base recipe
increases size by11t and both reflected depths by20t. These extra moves are
inserted before final reflection, so no compatibility of a transformed core
or of an abstract inherited spider labeling is assumed. The translated rows
therefore cover exactly[F7(p)+1,F8(p)] whenever this interval is nonempty.
The accepted D7 supplies2..F7(p); their union proves every depth through F8.
No C6 closure, new low-depth induction or search-completeness premise is needed.

The author's explanatory endpoint formula is also correct. For y=p-16>=45
and t=ceil(y/11), y<=11t and9t<=9(y+10)/11<=y. Every integer y in9t..11t
is a sum of t numbers from{9,10,11}. A seed16 construction thus reaches top
depth27+2y-2t=2p-5-2ceil((p-16)/11)=F8(p). This proves a top pair only;
the seven-row argument is still necessary for contiguous coverage at residue10.
Neither statement establishes optimality for the enlarged recipe family.

## Actual-spider transfer and parity

Every reflected core retains precisely the generic odd/even shell contract.
For odd k=2p+3 use M=4p+6,A=2p+2, selected core map Hx->M-x,Lx->x,
selected tail(3p+3,p+1,3p+4), partner pairs(2p+3+i,2p+1-i) for i0..p-1,
and partner tail(3p+6,p,3p+5). For even k=2p+4 use M=4p+8,A=2p+4,
selected tail(3p+5,p+2,3p+7,p+3), partner pairs(2p+5+i,2p+3-i), and
partner tail(3p+6,p,3p+8,p+1). The accepted shell partitions give every
label0..M and weight1..M once and put every edge across the cut A. No
surviving insertion window or prescribed zero-pair orientation is required.

For h=n-2,Q=hk+m, the residual spider center is0, arm i has odd-depth
labels(h-i)k-(t-1)/2 and even-depth labels ik+t/2, and short leaves have
labels hk+1..Q. The low/high intervals partition1..hk; center-edge weights
are the multiples of k and internal edges fill the intervening open blocks.
Leaves complete labels and weights through Q. This includes h0 and Q0.
Add A to residual noncenter labels and add Q to shell labels above A,
identifying the centers. The full label bands partition0..N and the edge
weights partition1..Q and Q+1..N, where N=nk+m.

The chosen L0 stays0 and H0 becomes N. Complement the entire graph by N-x
when requesting H0. The seven new recipes have L0,H0 order, but the argument
also covers H0,L0; the latter is explicitly tested using the inherited p21
seed with q10/q11 words. Core positions are unchanged because tails append
vertices and do not count the center. Any requested arm can be selected and
has a distinct partner for n>=2. Thus the quantifiers are actual arbitrary
spiders and selected arms, not just the n2,m0 path case.

The same p=floor((k-3)/2) corresponds to odd k=2p+3 and even k=2p+4.
Therefore p>=61 is exactly k>=125 with neither parity omitted. Earlier
lengths inherit D7. Both zero-pair targets and both shell parities pass BFS.

## Bounds and precise improvement

The residue gains above are independent of a and of shell parity. F8 rises
by2 within a block and is constant from r10 to the next r0. It is therefore
nondecreasing; at p61 it agrees with D7, so the piecewise low/high join is
also monotone. First improvement is k127/128:107 becomes109. At k145/146,
123 becomes127. Adding22 to k and20 to depths repeats each example.

For k=2p+3+epsilon,epsilon0/1, exact subtraction gives

    10k-11D8(k)=73-2r+10epsilon,  k>=125.

The new-branch range is53..83. The inherited k19..124 branch retains its
largest deficit261 at k124. Thus0<=10k-11D8<=261 globally, all asserted
depths are strictly less than k, and
0<=10/11-D8(k)/k<=261/(11k). This proves the unchanged all-integer10/11
limit. No new fixed-depth inverse is claimed or required by this package.

## Separate execution and negative controls

The final normal and optimized runs are byte-identical PASS. The new auditor
rechecks all three gadget side/sum identities, exact seed copies, seven recipe
sizes/depths and exact gap unions. It constructs the seven recipes at extra
q11 counts0,1,3,8,20 and, where distinct, forward, reversed and rotated move
orders. This checks additive tracking with different insertion orders.

For every resulting core, both shell parities, both zero-offset depths,
(n,m) in{(2,0),(2,4),(3,0),(4,3),(7,2)}, and selected arms0,floor(n/2),n-1
(deduplicated) are checked. There are4,420 recipe spiders. Five extra mixed
words on seed21 test the H0,L0 orientation in both parities, n2,m0 and n3,m5,
both exterior arm choices and both depths, giving80 additional spiders.
In total4,500 actual graphs pass complete label/edge permutations and BFS;
91 constructed cores,986 graph insertions and6,757 core-contract checks pass.

The finite arithmetic diagnostics cover99,940 sizes p61..100000 and199,982
lengths k19..200000. They check residue translation, gain table, top-pair
formula, monotonicity, legal depths and exact deficit identities. The
unbounded theorem rests on the universal identities and translation argument,
not on extrapolation from these ranges.

Seventeen explicit negative controls reject: a changed P entry for each of
the three gadgets; wrong recipe size; wrong reflected depth; either incomplete
single-pair substitute at residue10; premature reflection before insertion;
substitution of ordinary zero shifts for reflected shifts; partial complement,
duplicate labels and reversed selected arms in each shell parity; a wrong
requested depth; and n1. Every rejection remains active under python -O.

Replay with standard Python:

    python -B audit.py
    python -B -O audit.py

source-inputs.json binds every author file, inherited proof inputs and copied
auditor code provenance. Hashes are checked before and after the final runs.
Our manifest binds source, report, provenance and both result files. Author
run counts are not substituted for this separate evidence.

## Verdict and scope limits

**GO** for the exact D8 prescribed-zero theorem, all seven recipes and every
translated residue, both shell parities and zero targets, all n>=2,m>=0 and
selected arms, the precise gain table, monotonicity, legal depths, deficit261
and unchanged10/11 limit. The inherited D7 and generic insertion/shell results
remain explicit authenticated premises. Historical priority, external review,
Lean formalization, unrestricted near-tip coverage and optimality remain
unestablished. No public or shared-file write was performed.
