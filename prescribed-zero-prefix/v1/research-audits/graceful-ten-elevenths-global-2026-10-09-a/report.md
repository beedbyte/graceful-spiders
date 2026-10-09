# Private all-integer prescribed-zero prefix tending to 10/11

9 October 2026. Author mathematical construction and executable verification.
The q11 gadget now has a separately frozen internal acceptance, bound in
inputs.json. The new global prefix proof in this package awaits its own separate
internal audit. This is private research evidence, with no public release,
external review, formal proof-system verification, optimality or historical
priority claim. Jordi Gartner publishes the work through Beedbyte. AI assistance
supported the interval derivation, proof construction and executable checks here.
Historical inputs, shared checkpoints, CMS content and profiles remain unchanged.

## 1. Exact sufficient theorem

For k>=19 let p=floor((k-3)/2). Use the accepted D6 bound for k<125:

    D6(k)=11                              (19<=k<=34),
          27                              (35<=k<=52),
          25+16 floor((k-35)/18)           (k>=53).

For p>=61 write p=61+11a+r, with a>=0 and 0<=r<=10, and define

    F(p)=107+20a+4 floor(min(r,9)/2).

The eleven increments within a block are

    r:       0  1  2  3  4  5  6  7  8  9 10
    F-base:  0  0  4  4  8  8 12 12 16 16 16.

Set D7(k)=D6(k) for19<=k<=124 and D7(k)=F(p) for k>=125.
For every n>=2,m>=0, every selected long arm of S(k^n,1^m), and every
integer depth 2<=d<=D7(k), there exists a graceful labeling that assigns
zero to the specified actual vertex at that depth. The labeling may depend
on the requested vertex. Both arm-length parities and m=0 are included.

D7 never regresses from D6. Its first strict improvement is k125/126:
105 becomes107. It satisfies

    0 <= 10k-11D7(k) <=261,
    D7(k)/k ->10/11 through all integers.

The bound is a sufficient prefix. It claims neither full zero-rotatability,
depth1, optimality, nor existence at every depth above the prefix.

## 2. Exact tracked-depth intervals at every core size

The six frozen seeds have sizes16+delta, delta=0,...,5, and reflected
maximum-pair first depths

    b_delta=[26,26,26,26,24,27].

The first five reflected pairs are L0,H0 and the last is H0,L0. Every
initial maximum pair lies entirely before the compatible H4,L0,H0,L1 window.
The accepted q9 P2/P4 insertions have reflected gains16/14 and size gain9.
The separately accepted q11 P2 literal has reflected gain20 and size gain11:

    P=[3,8], B=[11,10,5,5,4,2,3,4],
    D=[1,1,2,6,6,7,7,9,10,8,9,11].

Its three replacement chains have sums[1,23] union{26}; each tagged side
supplies1,...,11 once. Positive old entries shift by11, zero entries stay
zero, and the two removed sums1,4 are filled by the chains. The compatible
window and endpoints persist. The maximum pair stays before the window and
its first index grows by len(P)=2. Reflection T(C)[i]=p-1-C[2p-1-i]
therefore advances its first zero depth by22-2=20. These are the exact
universal premises established in the bound q11 audit, not search statuses.

For any target p>=16 choose any a,j>=0 with11a+9j<=p-16. Define

    delta=(p-16-11a-9j) mod6,
    h=(p-16-11a-9j-delta)/6.

Start at seed16+delta, insert a q11 gadgets and j q9 gadgets, apply the
final reverse-complement, and append h translated C6 blocks. If exactly s
of the q9 moves are P2, where0<=s<=j, the two attainable depths are

    b_delta+20a+14j+2s and b_delta+20a+14j+2s+1.

Varying s supplies exactly the full integer interval

    I(p;a,j)=[b_delta+20a+14j, b_delta+20a+16j+1].        (1)

Thus the union of (1) over these a,j is the exact set of tracked pair depths
for this specified recipe family. Order of the insertions does not alter
these depths. This family uses these SIX seeds, q11 P2, q9 P2/P4 and final
C6 appends; it does not include q10, other seeds, other constructions, or
other sources of prescribed zero. Exactness here is not graph-theoretic
optimality and is not an all-gadget claim.

The append block is C6=[3,3,2,1,1,0,0,4,4,5,5,2]. Appending x+C6 at
size x adds both side ranges x,...,x+5, internal sums2x,...,2x+10 and
bridge sum(x-4)+(x+3)=2x-1. Its new endpoint is(x+6)-4. Its positive
entries leave the reflected zeros and depths unchanged. Appends occur AFTER
reflection; no commutation of those operations is assumed.

## 3. Six starting sizes and eleven exact interval bridges

An interval recipe is listed as(a,j,delta); every table row below has h=0.
The displayed chains directly cover all integers from the inherited bound
through the new endpoint. For p61,...,66, D6=105.

| p | Recipes | Intervals | F(p) |
|---|---|---|---:|
|61|(0,5,0)|96..107|107|
|62|(0,5,1)|96..107|107|
|63|(0,5,2),(1,4,0)|96..107,102..111|111|
|64|(0,5,3),(1,4,1)|96..107,102..111|111|
|65|(1,4,2),(2,3,0)|102..111,108..115|115|
|66|(0,5,5),(1,4,3),(2,3,1)|97..108,102..111,108..115|115|

The next table covers[F(p-6)+1,F(p)] at each p67,...,77.

| p | Required band | Recipes | Available interval chain |
|---|---|---|---|
|67|108..119|(1,4,4),(2,3,2),(3,2,0)|100..109,108..115,114..119|
|68|108..119|(1,4,5),(2,3,3),(3,2,1)|103..112,108..115,114..119|
|69|112..123|(2,3,4),(3,2,2),(4,1,0)|106..113,114..119,120..123|
|70|112..123|(2,3,5),(0,6,0)|109..116,110..123|
|71|116..123|(0,6,1)|110..123|
|72|116..127|(0,6,2),(1,5,0)|110..123,116..127|
|73|120..127|(0,6,3),(1,5,1)|110..123,116..127|
|74|120..131|(0,6,4),(1,5,2),(2,4,0)|108..121,116..127,122..131|
|75|124..131|(0,6,5),(1,5,3),(2,4,1)|111..124,116..127,122..131|
|76|124..135|(1,5,4),(2,4,2),(3,3,0)|114..125,122..131,128..135|
|77|124..135|(1,5,5),(2,4,3),(3,3,1)|117..128,122..131,128..135|

Every p>=67 is uniquely p0+11t with67<=p0<=77,t>=0. Add t q11 moves
to each recipe in its p0 row BEFORE reflection. Its size grows by11t,
and its whole interval grows by20t. Since F(x+11)=F(x)+20, the translated
chain covers exactly the required band[F(p-6)+1,F(p)]. All counts remain
nonnegative. This proves the bridge for every p>=67 without residue gaps.

For rigor about low depths, this induction constructs a *core* for every
depth90,...,F(p), rather than trying to append to an arbitrary inherited
full-spider labeling. At each base p61,...,66 the accepted D6 construction
supplies endpoint-compatible cores through depth105: it uses its accepted
D5 core prefix through depth101 plus the reflected q9 interval97..105.
Only depths90..105 are needed for this starting contract. The displayed
base chains extend these cores through F(p).

Now induct by6. Given a core for every depth90..F(p-6), append one C6
to preserve those depths at size p. The translated bridge supplies every
remaining depth through F(p). This proves the core interval90..F(p) for
all p>=61. At every such p the accepted D6 prefix is at least105, so its
actual-spider labelings cover2..89 and overlap this new core interval.
This closes the full prefix using only a verified core-level induction.

## 4. Optional exactness within the specified recipe family

This section is separate from the existence theorem. At p>=61, union the
accepted D6 depth prefix with the tracked-depth recipe family in section2.
Its maximal contiguous prefix is exactlyF(p). This does not include q10
or any other unlisted seed/gadget/labeling recipe.

For an interval upper endpoint H and recipe(a,j,delta,h), eliminate a:

    11H-20p=c_delta-4j-120h,
    c_delta=[-23,-43,-63,-83,-125,-112].

The eleven F defects11F(p)-20p at p61,...,71 are

    [-43,-63,-39,-59,-35,-55,-31,-51,-27,-47,-67].

If h>=1 or j>=12, then11H-20p<=-71<-67, so H<F(p). For the remaining
h0,j0..11,delta0..5, the size constraint requires

    delta+9j = p-16 (mod11).

These72 elementary candidates across the11 target residues give no endpoint
aboveF except when p=5(mod11). There the sole candidate aboveF is
delta0,j0, giving the isolated pair[F+3,F+4]. Every other endpoint is at
mostF. A negative formal value of a may be retained in this modular check
as an upper-bound relaxation; removing infeasible recipes cannot enlarge
the attainable set. For p>=61 in this special residue, the isolated pair's
actual a is nonnegative, so the obstruction is real. DepthF+1 is missing
from this recipe union despite the higher pair.

The accepted D6 endpoint is also at mostF. To prove that unboundedly,
check p61..159 explicitly using the two formulas; all99 differences are
nonnegative. Under p->p+99, F grows180 and D6 grows176. Thus the difference
grows4 and the99 residue check proves nonregression for all p>=61.
The finite calculations in this section are exact integer certificates,
not extrapolations of numerical behavior.

## 5. Actual spiders, orientations, and all integer k

The core has endpoints H3,L(p-4), both tagged permutations0..p-1, and
edge sums0..2p-2. Both accepted shell formulas therefore apply. For odd
k=2p+3 set M=4p+6,A=2p+2. Map the selected core Hh to M-h and Ll to l,
then append(3p+3,p+1,3p+4). The partner arm consists of the p pairs
(2p+3+i,2p+1-i), i0..p-1, followed by(3p+6,p,3p+5).

For even k=2p+4 set M=4p+8,A=2p+4. Use the same core map, selected
tail(3p+5,p+2,3p+7,p+3), partner pairs(2p+5+i,2p+3-i), followed by
(3p+6,p,3p+8,p+1). Each shell labels its two-arm path0..M, has distinct
weights1..M, and every edge crosses the cut A. These facts follow from
the accepted generic shell partitions, which require no ordering of the
zero pair and no surviving insertion window after reflection.

For arbitrary n>=2,m>=0, choose the requested arm and any distinct partner.
Put h=n-2,Q=hk+m,N=nk+m. For residual arm i0..h-1, label odd depth t by
(h-i)k-(t-1)/2 and even depth t by ik+t/2; short leaves receive hk+1..Q
and residual center0. These label and weight ranges are0..Q and1..Q.
Add A to residual noncenter labels, identify its center with shell centerA,
and add Q to shell labels aboveA. The complete graph has labels0..N once
and weights1..N once: residual weights are1..Q and shell weights Q+1..N.

At the selected L0 member the label is0; at H0 it isN. Complement the
ENTIRE graph by N-x if the H0 member is requested. This handles both
L0,H0 and H0,L0 pairs, including the p21 seed's odd first depth. Core
entries are at the same actual center distances: shells append tails and
do not count the center in the core indices. Arbitrary arm choice follows
by naming the requested arm before assigning the shell. The n2,m0 case
has Q0 and is included. For both parity shells, p=floor((k-3)/2), so the
piecewise theorem contains every k with no parity exception.

## 6. Quantitative bound and inverse threshold

For p=61+11a+r and k=2p+3+epsilon,epsilon0/1,

    10k-11F(p)=73+20r+10epsilon-44 floor(min(r,9)/2).

The eleven residues and two parities give57..107. For k19..124, direct
evaluation of the inherited finite pieces gives maximum261 at k124.
This proves0<=10k-11D7<=261 globally and the all-integer10/11 limit.
In particular D7<k, so all asserted depths are legal. D7 is nondecreasing.

A sufficient all-k fixed-depth threshold, exactly inverse to this D7, is

    K7(d)=19                         for2<=d<=11,
          35                         for12<=d<=27,
          35+18 ceil((d-25)/16)      for28<=d<=89.

For d>=90 define

    a=max(0,ceil((d-123)/20)),
    s=max(0,ceil((d-107-20a)/4)),
    K7(d)=125+22a+4s.

Here0<=s<=4. The plateau values and monotonicity show that every integer
k>=K7(d) has D7(k)>=d, while K7(d)-1 (if at least19) does not. This is
the inverse of this sufficient bound, not a least graph-theoretic threshold.

## 7. Executable scope and source binding

verify.py is a standard-library, read-only checker using explicit exceptions.
It checks all bound input SHA256 values before reading the seeds. It verifies
the three literal gadgets, the six exact seed cores, every base and bridge
interval, the99 nonregression cases, the finite modular endpoint bound, and
the finite deficit calculation. It builds every s choice in the finite table
recipes and their translations by1 and7 q11 moves. Separate extra cases
append two C6 blocks, exercising all six seed residues after reflection.

For those actual cores it constructs named spiders, complete label and edge
partitions, and BFS distances. The main matrix uses both shell parities,
(n,m)=(2,0),(3,2),(5,0), selected arm0 and n-1, and both zero-pair depths.
Additional padded cases use n3,m0,selected arm2 and both depths/parities.
The diagnostic exact-union check covers p61..500. The theorem follows from
the unbounded interval/induction/partition arguments above; this finite matrix
is supplementary executable evidence. No new negative-control suite is claimed.

Run python -B verify.py and python -B -O verify.py. The saved normal and
optimized JSON outputs must match. Their counts and exact interval recipes
are retained in the files. inputs.json binds every historical input used.
The q11 separate GO report is
f90b3ef57a1f9d9f762f99a2db7b68eef8d88c1862e35809794122e54be33a44;
its manifest is720ef06b23bf2a7a5cc39dd02d260f519ac0939ad58e69be73f747ebe1ef4afd.
The accepted D6 report is
d018ad8ffba50cf53a6d1f78e34df406285985a9b4c58098f485773a9ed4c7d6.
All other exact bindings and this package's hashes are in inputs.json and
manifest.json. This author proof awaits a separate global-theorem audit.
