# Compatible seeds improve the all-odd prescribed-zero prefix

Private author construction, 9 October 2026. Author mathematical verdict:
**positive theorem candidate; separate internal mathematical audit pending**.
No external review, public release, worldwide priority claim, or Lean proof.
Jordi Gartner owns and publishes the work through Beedbyte. AI assistance in
this private task supported the finite seed search, proof construction and
separate executable checks documented here.

## Exact theorem

For odd k>=19 define

    D5(k)=11                                  if 19<=k<=33,
    D5(k)=27+14U+2 floor(U/2), U=floor((k-35)/18) if k>=35.

For every n>=2, m>=0, every specified long arm of S(k^n,1^m), and every
integer d in 2..D5(k), there exists a graceful labeling assigning zero to
the specified depth-d vertex. Different requested vertices may use different
labelings. Center and depth one can be covered by the earlier separate
formulas; no full all-odd zero-rotatability is inferred here.

Equivalently, for d>=12 let

    u(d)=min {u>=0 : d<=27+14u+2 floor(u/2)},
    K5(d)=35+18u(d),

and let K5(d)=19 for 2<=d<=11. Every odd k>=K5(d) has the stated
prescribed-zero property. The target is a legal vertex: for k>=35,
D5(k)<=27+15U<35+18U<=k. For small k, 11<19<=k.

For d in12..27, u=0. For d>=28 write d-28=30q+r, 0<=r<30;
then u=2q+1 if r<=13, and u=2q+2 otherwise.

## Exact seed certificates

`seeds.json` contains 48 ordered integer arrays C(p0,a), one for every
p0=16,...,21 and every a=12,14,16,18,20,22,24,26. Each has length2p0,
alternating H,L beginning H. Each tag side separately permutes0,...,p0-1,
and its adjacent numeric sums permute0,...,2p0-2. The endpoints are
H3,L(p0-4), and positions a-1,a,a+1,a+2 (one based) are precisely
H4,L0,H0,L1. Thus each array satisfies the full universal insertion
contract, rather than merely being a graceful core.

These arrays are finite arithmetic certificates. Solver feasibility statuses
are not proof premises. `check.py` checks all their entries and the complete
48-member grid without importing the solver or constructor. For example,
the p0=16,a=26 certificate is

    [3,4,2,3,5,7,8,5,6,8,9,9,12,13,14,14,15,15,11,11,
     13,10,10,6,4,0,0,1,1,2,7,12].

The p9..14 searches and p8 negative solver statuses saved alongside the
package are exploratory only and are not used for this theorem.

## Unbounded extension and interval proof

Use the six frozen q9 gadgets with displacement4,6,...,14 and the q18
gadget with displacement30 from the accepted B+ package. For clarity the
proof applies their universal core lemma directly to the new seeds; it does
not call the original B+ theorem with its depth8 base.

For each gadget G=(P,B,D), q in{9,18}, and input core C with low zero at
zero-based index z, replace it by

    P ++ (q+C[:z]) ++ B ++ [0,0] ++ D ++ (q+C[z+2:]).

All entries outside the two zeros are positive. The new tagged side entries
from P,B,D each permute1,...,q; retained old positives shift to q+1,...,p+q-1.
The retained sums are {0} union ([2q+2,2p+2q-2] minus{2q+4}).
The three replacement chains P,H(q+3); H(q+4),B,L0; H0,D,L(q+1)
have sums precisely[1,2q+1] union{2q+4}. The endpoints, alternating tags
and H4,L0,H0,L1 window persist. Thus the size becomes p+q and the zero
anchor moves by len(P)+len(B). `check.py` directly checks these side and
sum identities for all seven literal gadgets.

After j units of size9, pair them as j=2b+e, e in{0,1}. Each paired unit
allows every even displacement8,...,30: two q9 gadgets give8,...,28,
and the q18 gadget gives30. The remaining single unit, if present, allows
4,...,14. Integer interval addition therefore gives every even displacement

    4j,...,14j+2 floor(j/2).

Each seed anchor12,14,...,26 consequently produces all integer depths in

    J_j=[12+4j, 27+14j+2 floor(j/2)]

by using the adjacent zero/max pair in the actual-spider transfer. There
are no parity gaps: the even anchor intervals from successive seeds overlap,
and each final even anchor covers itself and the following odd depth.

Fix a target p>=16 and any j<=U=floor((p-16)/9). Divide

    p-(16+9j)=6r+delta, r>=0, 0<=delta<=5.

Choose p0=16+delta. Start from the desired seed C(p0,a), apply the j
extension units, and append r copies of the translated six-core

    C6=[3,3,2,1,1,0,0,4,4,5,5,2].

The append keeps old zeros and their positions. At current size x, its
bridge sum is (x-4)+(x+3)=2x-1, its internal sums are2x,...,2x+10,
and each new side contributes x,...,x+5. Endpoints become H3,L(x+2),
exactly the required endpoints at size x+6. Thus each J_j is available
at every target p>=16+9j, without omitted size residues.

J_0 is12..27. The old thirty small cores and C6 give2..11 at every p>=8.
For j>=1, previous upper minus current lower is

    27+14(j-1)+2 floor((j-1)/2) -(12+4j)
      =1+10j+2 floor((j-1)/2)>=11.

Therefore 2..11 and J_0,...,J_U form the entire prefix2..D5(k),
where k=2p+3. This is an unbounded integer proof.

## Actual named spider transfer

For a size-p core put k=2p+3,M=4p+6,A=2p+2. Give the center label A.
On the selected arm send Hh to M-h and Ll to l, then append
[3p+3,p+1,3p+4]. On the partner arm use the pairs
(2p+3+i,2p+1-i), i=0,...,p-1, then[3p+6,p,3p+5].
As in the accepted q18 proof, these two arms and center partition0,...,M,
their differences partition1,...,M, and all edges cross A. Specifically,
selected differences are{2p+1},[2p+8,4p+6],{2p+7,2p+2,2p+3}; partner
differences are[1,2p],{2p+4,2p+6,2p+5}.

For h=n-2,Q=hk+m, add Q to path labels above A. Insert remaining long
arms indexed i=0,...,h-1 with their depth-t labels

    A+(h-i)k-(t-1)/2   for odd t,
    A+ik+t/2           for even t,

and short leaves A+hk+1,...,A+hk+m. The residual labels partition A+1,...,A+Q
and their differences partition1,...,Q; path differences shift toQ+1,...,Q+M.
The selected paired zero entries become0 and N=nk+m at the adjacent depths.
If the requested vertex has N, complement the entire spider x->N-x.
This works for any chosen long arm, n>=2,m>=0, including h=0 and Q=0.
The construction and checker use actual named spider vertices and edges.

## Pointwise comparison

For k>=35 write p=16+9U+r,0<=r<=8. V4's T=floor((p-8)/9) is U if
r=0 and U+1 if r>=1. For U>=1 the new bound exceeds v4 by18 at r=0,
by4 at r>=1 with U even, and by2 at r>=1 with U odd. At U=0,r=0
(k35), the improvement over max(11,9) is16; at U=0,r>=1 it is4.
Hence D5 is strictly stronger at every odd k>=35 and unchanged at19..33.
The asymptotic ratio remains5/6; no improved limiting fraction is claimed.

For every d>=12, v4's minimum t(d) is u(d)+1 or u(d)+2. This follows
from old H(u)=9+14u+2 floor(u/2)=new H(u)-18, old H(u+2)=new H(u)+12,
and minimality of u (with u=0 checked directly). Therefore

    K_v4(d)-K5(d)=2 or20.

Examples: depths12..23 have K5=35 versus37; depths24..27 have35 versus55;
depths28..39 have53 versus55; depths40..41 have53 versus73.
Existing complete fixed-length theorems at k21 and k27 remain stronger
at those two particular lengths. They do not establish a uniform statement
for every subsequent odd length; the new thresholds do not claim an
improvement over their complete coverage at k21 or k27.

## Executable checks and freeze boundary

In a writable copy with standard Python:

    python -B construct.py
    python -B check.py
    python -B -O check.py

The separate checker imports neither construct.py nor OR-Tools. Both modes
must match:48 compatible seeds,7 symbolic gadget identities,4,786 final cores,
3,252 actual spiders,985 arithmetic target sizes, and4 rejected corruptions.
Core certificates cover every requested depth at p8..80. Actual spider
certificates cover every requested depth at p in{8,15,16,17,21,24,25,33,34,
35,43,44,52}, each (n,m) in{(2,0),(3,2),(5,1)} and arms0,n-1. A BFS
rechecks center distances and the prescribed zero, alongside full label and
edge-difference permutations. Finite checks diagnose the proof; the universal
claim rests on the explicit seeds, insertion identities, interval addition,
residue division, C6 append and actual-spider transfer above.

The new search used one CP-SAT worker, seed1, two seconds per finite model.
No q24 model or unresolved q24 case was rerun. No solver INFEASIBLE result
is used as an obstruction theorem. `source-inputs.json` binds predecessor
inputs; `manifest.json` binds this frozen package. RESTART and cycle files
were not edited. Separate internal mathematical reconstruction, formalization
and primary-literature comparison remain required before any release decision.
