# Separate internal mathematical audit of the 10/11 prefix

Private record, 9 October 2026. **GO for the exact all-integer D7 theorem,
its quantitative and inverse-threshold claims, and the explicitly restricted
recipe-family exactness claim in the frozen author report bound below.**
This is a separate internal mathematical reconstruction and implementation,
not external review, peer review, a Lean proof or a priority determination.
Jordi Gartner owns and publishes the work through Beedbyte. AI assistance
supported the proof reconstruction, graph implementation and checks recorded
here. No shared checkpoint, historical artifact or public content was changed.

## Accepted statement and bindings

For every integer k>=19, set p=floor((k-3)/2). Let D6(k) be11 at19..34,
27 at35..52, and25+16floor((k-35)/18) thereafter. Set D7(k)=D6(k) at
19<=k<=124. For k>=125 write p=61+11a+r, a>=0,0<=r<=10, and set

    D7(k)=F(p)=107+20a+4 floor(min(r,9)/2).

For all n>=2,m>=0, every specified long arm of S(k^n,1^m), and each integer
2<=d<=D7(k), a graceful labeling exists with zero at the specified depth-d
vertex. Different requests may use different labelings. Both k parities and
m0 are included. Moreover D7>=D6, 0<=10k-11D7<=261, and D7(k)/k tends
to10/11 through all integers. These are sufficient depths, not an optimal
graph-theoretic prefix or a full zero-rotatability claim.

Frozen author directory: graceful-ten-elevenths-global-2026-10-09-a.

| Artifact | SHA-256 |
|---|---|
| report.md | `bf7eec616fa42a5465703e4f90d296f02dcb35a0b91c5c6c82bdfcf5208f9249` |
| manifest.json | `419634baa520139e83395fb2014478710317d8bf72f83c4c7c54e31083be739d` |
| verify.py | `8d3e1321bdbbf1477d86b8fa0ad4816555dd9897735fbefec82024347b2c38d2` |

The accepted q11 universal-gadget audit report is
`f90b3ef57a1f9d9f762f99a2db7b68eef8d88c1862e35809794122e54be33a44`,
with manifest `720ef06b23bf2a7a5cc39dd02d260f519ac0939ad58e69be73f747ebe1ef4afd`.
The accepted D6 audit is the earlier report
`d018ad8ffba50cf53a6d1f78e34df406285985a9b4c58098f485773a9ed4c7d6`.
source-inputs.json binds these, all author payloads and historical inputs.

## Independence and universal local premises

AGENTS.md and EDITORIAL_POLICY.md were followed. The new author report and
numeric verification tables were read only after its announced freeze.
Author Python files were hashed but neither read, executed nor imported.
The audit uses only the standard library. core_graph.py is an exact copy of
this auditor's previously frozen independent graph implementation; its
provenance is recorded rather than represented as a second new implementation.
It inserts by deleting/subdividing tagged edges, checks degrees/connectivity,
and traverses the resulting path. Spider adjacency and BFS are independent
of label assignment. No solver or new search result is a proof premise.

The six original compatible seeds have (p,old-zero-depth) keys
(16,16),(17,22),(18,22),(19,20),(20,24),(21,22). Each side permutes0..p-1,
all neighboring sums permute0..2p-2, the endpoints are H3,L(p-4), and the
window is H4,L0,H0,L1. The maximum pair is before the zero window. Their
reflected first zero depths are b=[26,26,26,26,24,27]. The first five pairs
are L0,H0 and the last is H0,L0. Both orders are retained throughout this audit.

The q9 P4/P2 gadgets have size gains9 and reflected gains14/16. The q11
literal is

    P=[3,8], B=[11,10,5,5,4,2,3,4],
    D=[1,1,2,6,6,7,7,9,10,8,9,11].

Its new tagged sides each permute1..11, and P,H14; H15,B,L0; H0,D,L12
have sums1..23 and26 exactly once. It therefore fills the complement of
retained sums {0} union ([24,2p+20] minus{26}). All entries outside the
old zero pair are positive. The new size is p+11, endpoints H3,L(p+7),
and the same compatible window persists. The old maximum pair becomes
p+10,p+10, exceeds all new offsets, and stays before the zero window.
Its first index advances by2, so reflection advances its first depth by20.

Reflection is T(C)[i]=p-1-C[2p-1-i] with newly assigned alternating tags.
Source tags swap because2p-1 is odd; both target sides are permutations.
Sums become2p-2-s and endpoints remain3,p-4. If the maximum pair begins
at index t, the zero pair after reflection is at depths2p-1-t,2p-t.
Thus order of the q9/q11 moves does not change the tracked depths, and all
moves must precede reflection because T need not preserve the local window.

Finally, at size x append x+C6 where
C6=[3,3,2,1,1,0,0,4,4,5,5,2]. The new sides are x..x+5, bridge sum is
2x-1 and internal sums are2x..2x+10; endpoint becomes(x+6)-4. These
positive entries preserve both old zero positions. C6 occurs after reflection.

## Independent unbounded proof, derived before reading the author report

Represent a construction by its seed and a word of abstract recipe moves:

| Move | Size increase | Reflected depth increase |
|---|---:|---:|
| A: q9 with P length4 |9|14|
| B: q9 with P length2 |9|16|
| C: q11 with P length2 |11|20|
| P: final C6 append |6|0|

A word is compiled by performing A/B/C in its recorded order, reflecting,
then performing all P appends. In particular adding C to a word already
containing P means adding q11 before reflection in the recipe. It does NOT
mean applying a window-dependent insertion to the already reflected core.
The size and depth arithmetic is additive, and this compilation proves that
arbitrary recipe words remain valid.

The independent base-certificates.json contains371 literal core certificates:
every integer depth83..F(p) at each p61..71. Each certificate identifies the
original seed, complete move word, depth and resulting integer core. The
auditor checks every side/sum/endpoint contract and reconstructs each word
through graph insertion. A bounded dynamic program found these words, but
acceptance depends only on the explicit positive certificates; completeness
or correctness of that discovery algorithm is unnecessary.

Prove by strong induction that these recipes supply every depth83..F(p) for
all p>=61. The eleven base sizes are certified. For p>=72,

    F(p)=F(p-11)+20,    F(p-6)>=F(66)=115.

Appending P to recipes at p-6 supplies83..F(p-6). Adding C before reflection
to recipes at p-11 supplies103..F(p). The intervals overlap because115>=103.
For a requested d, use p-6 if d<=F(p-6); otherwise d-20>=96>=83 and
d-20<=F(p-11), so the p-11 branch is valid. Both source sizes are at least61
and smaller than p. This proves the unbounded claim without extrapolating
finite coverage or treating transformed cores as compatible insertion inputs.

For every p>=61, the accepted D6 prefix is at least105, so it overlaps
83..F(p). Therefore2..F(p) is covered after actual-spider transfer. This
independent argument directly validates the author's proposed upper function.

## Reconstruction of the author's six bases and eleven bridges

The frozen author's formula for a q11 count a and total q9 count j is

    delta=(p-16-11a-9j) mod6,
    h=(p-16-11a-9j-delta)/6,
    I(p;a,j)=[b_delta+20a+14j,b_delta+20a+16j+1].

Here a,j,h are nonnegative and delta0..5. Varying the number s of P2 q9
moves from0 through j gives starts in steps of2; including both zero-pair
members fills this entire DEPTH interval, for both b parities. Its upper
endpoint already includes the second member and receives no extra+1.

All six base table rows p61..66 and all eleven bridge rows p67..77 were
recomputed from the literal recipes in the saved verification table. Their
claimed endpoints and overlapping chains are correct, including one-step
adjacencies such as113 followed by114. Every table recipe has h0 and exact
size p=16+delta+11a+9j. The base chains connect the inherited core interval
90..105 to F(p). The bridge chains cover[F(p-6)+1,F(p)].

For any p>=67, choose the unique p0 in67..77 congruent to p modulo11.
Adding t=(p-p0)/11 q11 moves before reflection translates every interval
by20t, while F(p)=F(p0)+20t and F(p-6)=F(p0-6)+20t. Thus the whole
needed bridge is supplied at every p. Induction by6 preserves the earlier
core interval through C6 and fills its next band. At the starting sizes the
inherited D5 core interval through101 and reflected q9 interval97..105
supply actual cores through105; the induction does not append to an abstract
full-spider existence statement. The author's90..F(p) proof is consequently
sound and agrees with the independently established83..F(p) recipe interval.

## Actual spiders and every arm-length parity

Every constructed core has endpoints H3,L(p-4), both tagged permutations
and the full sum interval, which are precisely the accepted shell contracts.
For odd k=2p+3, take M=4p+6,A=2p+2; selected labels are M-c_i at even i
and c_i at odd i, followed by(3p+3,p+1,3p+4). The partner consists of
(2p+3+i,2p+1-i) for i0..p-1 and(3p+6,p,3p+5).
For even k=2p+4 use M=4p+8,A=2p+4, selected tail(3p+5,p+2,3p+7,p+3),
partner pairs(2p+5+i,2p+3-i) and tail(3p+6,p,3p+8,p+1).
In each shell the accepted band partitions give every label0..M and edge
weight1..M exactly once, with every edge crossing A. Neither shell assumes
an even first zero-pair depth or a surviving insertion window.

Choose the requested arm and any distinct partner. For h=n-2,Q=hk+m,
the residual arms have center0, odd-depth labels(h-i)k-(t-1)/2 and
even-depth labels ik+t/2; short leaves are hk+1..Q. These fill labels0..Q
and weights1..Q for all h,m, including h0,Q0. Add A to residual noncenter
labels and Q to shell labels above A. The resulting graph is exactly the
named spider, with labels0..N and weights1..N, N=nk+m. Each L0 is zero
and H0 becomes N; complement the entire graph when targeting H0.
Both consecutive depths work for the p21 H0,L0 pair as well as the other
five orientations. Tails leave core indices and actual BFS depths unchanged.

For odd k, p=(k-3)/2; for even k, p=(k-4)/2=floor((k-3)/2). Thus p>=61
is exactly k>=125, with no skipped parity. The accepted D6 handles19..124.

## Nonregression, legal depths, limit and the exact sufficient inverse

For p=61+11a+r, put h=floor(min(r,9)/2). The inherited endpoint is
D6=105+16floor((11a+r)/9). Its difference from F is

    F-D6=2+20a+4h-16floor((11a+r)/9).

For r<=9 write r=2h+e,e0/1. Using floor(x)<=x, this difference is at
least2+(4a+4h-16e)/9>=2/9. At r10,h4 the same lower bound is
2+(4a-16)/9>=2/9. The difference is an even integer, so F>=D6+2.
The author's alternative99-size periodic proof is also valid: p increases
by99 make F increase180 and D6 increase176, adding4 to the gap. The99
residue cases have minimum gap2. First improvement is k125/126:105 to107.

For k=2p+3+epsilon,epsilon0/1, direct subtraction gives

    10k-11F(p)=73+20r-44h+10epsilon.

The odd-parity values for r0..10 are
[73,93,69,89,65,85,61,81,57,77,97]; even parity adds10. Thus new-branch
deficits are57..107. The inherited branches at k19..34,35..52,53..124 have
deficits10k-121,10k-297 and75+4U+10r respectively, with U1..4 and r0..17.
Their maximum is261 at k124. Hence globally0<=10k-11D7<=261, so D7<k
and0<=10/11-D7/k<=261/(11k). This proves the claimed all-integer limit.

The within-block F increments are[0,0,4,4,8,8,12,12,16,16,16], and the
next block starts4 above the preceding endpoint. Together with the join at
k125, D7 is nondecreasing. The author's sufficient inverse is correct:

    K7(d)=19                            for2<=d<=11,
          35                            for12<=d<=27,
          35+18ceil((d-25)/16)           for28<=d<=89.

For d>=90, put a=max(0,ceil((d-123)/20)) and
s=max(0,ceil((d-107-20a)/4)); then K7(d)=125+22a+4s.
The choice a selects the first block whose upper endpoint123+20a reaches d.
Within it s0..4 selects the first plateau107+20a+4s reaching d. Its first
size is p61+11a+2s and first length125+22a+4s. The preceding length fails
the bound, including the initial90..107 plateau after k124's endpoint89.
This is exactly the inverse of D7, not a least existence threshold.

## Optional restricted exactness claim

This acceptance also covers author section4, strictly within the listed six
seeds, q9 P2/P4, q11 P2 and final C6 recipe family union the D6 prefix.
It does not cover q10, other seeds, other gadgets or unrestricted labelings.

For any recipe upper endpoint H, eliminating the q11 count yields

    11H-20p=c_delta-4j-120h,
    c_delta=[-23,-43,-63,-83,-125,-112].

The eleven F defects are[-43,-63,-39,-59,-35,-55,-31,-51,-27,-47,-67].
If h>=1 or j>=12, the endpoint defect is at most-71 and hence below every
F defect. It suffices to inspect delta0..5,j0..11, with the necessary size
congruence delta+9j=p-16 mod11. Direct enumeration finds no higher endpoint
except delta0,j0 when p=5 mod11. That candidate's upper endpoint is F+4
and its lower endpoint F+3. Its q11 count is nonnegative for these p>=61;
nevertheless F+1 is missing. Every other recipe endpoint is at most F,
and D6<=F. The positive proof supplies every depth through F, so the union's
maximal contiguous prefix is exactly F. This finite modular certificate is
an unbounded restricted statement, not an optimality assertion about spiders.

## Executable evidence and limitations

audit.py verifies371 explicit base certificates, the recipe induction and
the universal gadget through the separate graph compiler. Its construction
checks include p61..160 plus172,183,200,250,500, both shell parities, n2/3/4/5,
m0/2/3, selected arms0,n-1 and an interior arm2, and each requested actual
depth. The base matrix gives4,452 BFS spiders; induction endpoints and seams
give940 more. The matrix checks83,103,F(p-6),F(p-6)+1,F(p), so both induction
branches and their overlap are exercised. It checks99,940 sizes p61..100000
and199,982 lengths k19..200000 for formula consistency and bounds.

check_author.py separately reconstructs every choice s in all six author
base rows and eleven bridge rows, at q11 translations t0,1,7. It verifies
the interval chains and checks the resulting actual spiders by full label
and edge permutations and BFS:603 table recipes and14,472 actual spiders.
Together the two programs check19,864 actual spiders. It also checks the finite modular certificate
and99,999 inverse thresholds d2..100000 at K7(d) and the preceding length.
All five author payload hashes match. Normal and optimized outputs match
byte for byte for both independent programs; final exact counts are in the
four frozen result files.

Thirteen controls in audit.py reject premature reflection before insertion,
wrong recipe size, an invalid base-size request, an excessive requested depth,
a corrupted q11 entry, append-before-reflect, ordinary/reflected shift confusion,
and partial complement, duplicate labels and reversed selected arms in both
shell parities. Two additional table controls reject a changed upper endpoint
and changed residue. All checks use explicit exceptions, so python -O retains
them. Author source was never executed; its saved run counts are not substituted
for these checks. The finite checks support the displayed unbounded proof.

Replay the frozen audit with standard Python:

    python -B audit.py
    python -B -O audit.py
    python -B check_author.py
    python -B -O check_author.py

All input bytes are checked before and after final execution. The manifest
binds our source, literal base certificates, report and result files. GO covers
the exact mathematical claims above, including section4 only with its explicit
recipe restriction. No mathematical defect or unresolved premise beyond the
authenticated inherited core/shell theorems was found. Historical priority,
external review, optimality, full zero-rotatability and Lean formalization of
this new theorem remain unestablished. No publication action is implied.
