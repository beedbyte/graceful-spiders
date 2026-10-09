# Graceful labelings with growing prescribed-zero prefixes in equal-arm spiders

**Beedbyte — technical manuscript, 9 October 2026.**

Jordi Gartner owns and publishes this work through Beedbyte. This distribution adapts the frozen technical manuscript v10. Its exact source versions and hashes are recorded in the accompanying README and source inventory.

## Abstract

For every integer k≥19 put p=⌊(k−3)/2⌋. Define D8(k)=11 for 19≤k≤34,27 for 35≤k≤52,and25+16⌊(k−35)/18⌋ for 53≤k≤124. For k≥125 write p=61+11a+r,a≥0,0≤r≤10,and set D8(k)=107+20a+2r. For all n≥2,m≥0,every selected long arm of S(k^n,1^m) and every depth2≤d≤D8(k), there exists a graceful labeling assigning zero to that vertex. Different requests may use different labelings; both arm-length parities and m=0 are included. Seven exact mixed q9/q10/q11 recipes, translated before classical reflection, fill the gaps above D7. The r10 four-depth gap needs two adjacent pairs. The bound satisfies D8≥D7 and0≤10k−11D8(k)≤261,hence D8(k)/k→10/11 through all integers. This adds bounded depths at infinitely many lengths without changing the limiting fraction. No optimality or full zero-rotatability is claimed.

## 1. Definitions and exact statements

All parameters are integers. An interval [a,b] contains its integer endpoints and is empty if a>b. S(k^n,1^m) has a distinguished center c, vertices v(i,d) for 0≤i<n and 1≤d≤k, and m additional leaves at c. Its long-arm edges are cv(i,1) and v(i,d)v(i,d+1). Thus its edge count is N=nk+m. Depth means actual graph distance from c, including the path case n=2,m=0.

A graceful labeling is a bijection f:V→[0,N] whose absolute edge differences biject [1,N]. An alpha labeling additionally has an index A such that every edge joins a label at most A to one greater than A. The midpoint label of an alpha path need not equal its index unless that equality is specified.

**Main theorem (D8 gap completion).** For every integer k≥19 set p=⌊(k−3)/2⌋. Use D8(k)=D7(k) for k<125. For k≥125 write p=61+11a+r, a≥0,0≤r≤10, and define F8(p)=107+20a+2r and D8(k)=F8(p). For every n≥2,m≥0, each selected long arm and each integer depth2≤d≤D8(k), there exists a graceful labeling of the actual S(k^n,1^m) assigning zero to the requested vertex. Different requests may use different labelings. Both parities and n2,m0 are included. D8≥D7, D8<k,0≤10k−11D8(k)≤261 and D8(k)/k→10/11 through all integers. These are sufficient bounds, not optimality or full zero-rotatability claims. The exact D8 mathematical audit is GO; D8 formal author and separate copied-source replay now have GO for the exact scoped theorem. No new fixed-depth inverse is claimed: the predecessor K7 remains sufficient because D8≥D7, but is not asserted to be the exact inverse of D8.
**Predecessor theorem (global q11 D7 prefix).** For every integer k≥19 put p=⌊(k−3)/2⌋. Define D7(k)=D6(k) for 19≤k≤124, using the predecessor function below. For k≥125, write p=61+11a+r, a≥0 and 0≤r≤10, and set

```
F(p)=107+20a+4⌊min(r,9)/2⌋;
D7(k)=F(p).
```

For every n≥2, every m≥0, every selected arm i with 0≤i<n and every integer d with 2≤d≤D7(k), there exists a graceful labeling f of the actual S(k^n,1^m) with f(v(i,d))=0. The labeling may depend on the requested arm and depth. Both length parities and m=0 are included. D7≥D6, D7<k and

```
0≤10k−11D7(k)≤261,
```

so D7(k)/k→10/11 through all integers. These are sufficient bounds, with no optimality, depth-one or full zero-rotatability assertion. Current mathematical acceptance is supported by the bound separate D7 audit; D7 formal author and separate copied-source replay packages now have GO for their exact scope; D8 formal author and separate copied-source replay are GO for the exact scoped theorem.

**Verified sufficient inverse.** For integers d≥2 define K7(d)=19 for 2≤d≤11, K7(d)=35 for 12≤d≤27, and K7(d)=35+18⌈(d−25)/16⌉ for 28≤d≤89. For d≥90 put

```
a=max(0,⌈(d−123)/20⌉);
s=max(0,⌈(d−107−20a)/4⌉);
K7(d)=125+22a+4s.
```

Here 0≤s≤4. Every integer k≥K7(d) satisfies the prescribed-zero conclusion for all n≥2,m≥0 and every selected long arm. K7 is the exact inverse of this sufficient prefix function, not a minimum over unrestricted graceful labelings.

**Predecessor theorem (all-integer D6 prefix).** For every integer k≥19, define

```
D6(k)=11,                            19≤k≤34;
D6(k)=27,                            35≤k≤52;
D6(k)=25+16U, U=⌊(k−35)/18⌋,          k≥53.
```

For every n≥2, every m≥0, every selected arm i with 0≤i<n and every integer d with 2≤d≤D6(k), there exists a graceful labeling f of the actual S(k^n,1^m) with f(v(i,d))=0. Different requested vertices may require different labelings. The bounds satisfy

```
0≤8k−9D6(k)≤191,
```

so D6(k)<k and D6(k)/k→8/9 through all integer lengths. Equivalently the sufficient fixed-depth thresholds are K6(d)=19 for 2≤d≤11, K6(d)=35 for 12≤d≤27, and K6(d)=35+18⌈(d−25)/16⌉ for d≥28. The conclusion holds for every integer k≥K6(d), all n≥2,m≥0 and every selected arm. Neither the thresholds nor the limiting fraction are asserted optimal. This is a contiguous long-arm prefix, not complete zero-rotatability or simultaneous zero assignment.

**Predecessor theorem (unified D5 prefix).** For every integer k≥19, define

```
D5(k)=11,                                  19≤k≤34;
D5(k)=27+14U+2⌊U/2⌋, U=⌊(k−35)/18⌋,        k≥35.
```

For every n≥2, every m≥0, every arm i with 0≤i<n and every integer d with 2≤d≤D5(k), there exists a graceful labeling f of the actual S(k^n,1^m) with f(v(i,d))=0. Furthermore D5(k)<k and

```
0≤5k−6D5(k)≤104.
```

Consequently D5(k)/k→5/6 as k→∞ through all integers, with no parity restriction.

**Equivalent sufficient threshold form.** Set K5(d)=19 for 2≤d≤11. For d≥12 let

```
H(u)=27+14u+2⌊u/2⌋,    u≥0;
u(d)=min{u≥0:d≤H(u)};
K5(d)=35+18u(d).
```

For every d≥2 and every integer k≥K5(d), the preceding conclusion holds for all n≥2,m≥0 and each selected long arm. The minimum is relative to H, not a minimum arm length among all graceful constructions. The labeling is existential **after** the requested arm and depth; this does not assert simultaneous zeros. Center, depth one, smaller lengths, unequal arms and depths above D5(k) are outside the predecessor statement. No nonexistence is asserted outside its bounds.

Earlier fixed-depth results are retained as source results: odd k≥3 permits depth 3; odd k≥5 permits depth 2; k=6s+3,s≥2 permits depths 2–11; and k=6s+3,s≥4 permits depths 12–22. Their complete proofs and narrower formal scopes remain in the [frozen v5 manuscript](verification-scope.md#source-records). Appendices A and B preserve its exact core tables; these older results are not inferred from a new claim below their bounds.

## 2. Exact cores and universal extensions

### 2.1 Weak and compatible contracts

A size-p core is a sequence of 2p numeric entries with alternating tags H,L starting H. Each tag separately permutes [0,p−1], consecutive numeric sums permute [0,2p−2], and endpoints are H3,L(p−4). Equal numbers with opposite tags are distinct vertices. This is the weak contract needed by either shell.

A compatible core additionally contains H4,L0,H0,L1 at one-based positions a−1,a,a+1,a+2, for an even a. Its low zero and high offset zero therefore lie at depths a,a+1 after shell construction. The new bank has exactly one core for every p0∈{16,…,21} and a∈{12,14,…,26}: 48 rows. Appendix C reproduces every ordered array and canonical compact-JSON hash from [seeds.json](research-audits/graceful-compatible-seed-prefix-2026-10-09-a/seeds.json), file SHA-256 `8ae0c7df38ef482cb9f41e3cd4b26a64f03f7643d3e352207a1d3358f403cb31`. Side permutations, sums, endpoints and the exact four-entry neighborhood are finite arithmetic certificates; solver status is not a premise.

For depths 2–11, the 30 older weak cores at p0=8,…,13 and a=2,4,6,8,10 suffice. They need not satisfy the stronger four-entry neighborhood. Their exact arrays and hashes are retained in Appendix B.

### 2.2 Universal q9/q18 surgery

The six inherited size-nine gadgets have displacements 4,6,…,14; the size-eighteen gadget has displacement 30. Their exact blocks P,B,D are bound in the B+ numeric sources and reproduced in Appendix D. For a compatible input C whose low zero has zero-based index z, let f(0)=0 and f(x)=x+q for positive x, and construct

```
P || f(C[0:z]) || B || [0,0] || D || f(C[z+2:2p]).
```

Each block has even length. P begins H3; B and D begin L, with B ending H4 and D beginning L1. The newly inserted numbers on each tag are exactly [1,q]. Old positive numbers become [q+1,p+q−1], while both old zeros remain zero. Each enlarged tag therefore permutes [0,p+q−1]. The first endpoint is H3 and the last L(p+q−4); the compatible neighborhood persists. Prefix attachment and replacement of two edges by internally disjoint chains preserve path topology. The anchor moves by len(P)+len(B).

The removed old sums are 4 and 1. The zero-zero edge retains sum 0; every other retained edge has two positive endpoints, so its sum increases by 2q. The retained sum multiset is

```
{0} ∪ ([2q+2,2p+2q−2] \ {2q+4}).
```

The inserted chains are P,H(q+3); H(q+4),B,L0; and H0,D,L(q+1). For every bound gadget their numeric sums are exactly [1,2q+1]∪{2q+4}, each once. They are disjoint from the retained sums and together partition [0,2(p+q)−2]. This proves the core extension universally, not by extrapolating a finite grid.

Two q9 steps add size 18 and give every even displacement 8,…,28. The q18 gadget gives the next displacement 30 at the same size. Hence a paired unit realizes 8+2c, 0≤c≤11. For j=2b+e, e∈{0,1}, use b paired units and e single q9 units. Subtracting minimum displacement and halving gives the sum of b integer intervals [0,11] and e intervals [0,5], exactly [0,11b+5e]. Thus total size increase 9j permits every even displacement in

```
[4j,14j+2⌊j/2⌋].
```

Starting with anchors 12,14,…,26 consequently gives every even anchor from 12+4j to 26+14j+2⌊j/2⌋: these equally spaced intervals overlap or meet on the even lattice. Adjacent low-zero/high-maximum pairs then cover every integer depth in

```
J_j=[12+4j,27+14j+2⌊j/2⌋].
```

### 2.3 Depth-preserving C6 append and complete residues

The exact block C6=(3,3,2,1,1,0,0,4,4,5,5,2) has both tag sides [0,5], endpoints H3,L2 and sums (6,5,3,2,1,0,4,8,9,10,7), a permutation of [0,10]. Append x+C6 to any size-x weak core. New tag bands are [x,x+5]; the bridge sum is (x−4)+(x+3)=2x−1; new internal sums are [2x,2x+10]. Together with [0,2x−2] they give [0,2(x+6)−2]. The new endpoint is L(x+2)=L((x+6)−4). Old zeros and their indices remain unchanged because all appended values are positive.

Fix p≥16 and any j≤⌊(p−16)/9⌋. Divide

```
p−(16+9j)=6r+δ,    r≥0, 0≤δ≤5.
```

Choose p0=16+δ, construct the required J_j core from its compatible seed by j units of insertion, then append r C6 blocks. Its size is precisely p0+9j+6r=p, with the selected depth pair unchanged. Every residue modulo six is covered. Similarly, for every p≥8, division p−8=6r+δ selects one of the six old p0=8+δ seeds and covers depths 2–11.

J_0 begins at 12 and ends at 27. For j≥1,

```
upper(J_(j−1))−lower(J_j)=1+10j+2⌊(j−1)/2⌋≥11.
```

Thus the small-depth block and J_0,…,J_U form the contiguous prefix [2,H(U)] at every p≥16, with U=⌊(p−16)/9⌋. This is the universal core-existence statement shared by both shells.

## 3. Odd and even midpoint-alpha shells

Both shells map core Hx to M−x and Lx to x in center-outward order on the selected arm. The weak core contract suffices; the shell does not assume a particular zero neighborhood or adjacent zero indices in an arbitrary input. The compatible bank specifically has low zero at even a and high offset zero at outward a+1.

### 3.1 Odd shell

Set k=2p+3, M=4p+6=2k and alpha index A=2p+2=k−1. Give the midpoint label A. Append (3p+3,p+1,3p+4) to the selected core arm. The partner arm consists of (2p+3+j,2p+1−j), j=0,…,p−1, followed by (3p+6,p,3p+5). Each arm has k vertices beyond the center.

Selected lows are [0,p−1]∪{p+1}, partner lows {p}∪[p+2,2p+1], and the center supplies A: together [0,A]. Selected highs are [3p+7,M]∪{3p+3,3p+4}; partner highs [2p+3,3p+2]∪{3p+5,3p+6}: together [A+1,M]. Every edge crosses A.

Selected differences are the center edge 2p+1, core interval [2p+8,M] and tail values 2p+7,2p+2,2p+3. Partner paired edges including its center edge give [1,2p]; its tail gives 2p+4,2p+6,2p+5. These partition [1,M]. Thus the path is alpha graceful with the required midpoint/index equality and depth preservation.

### 3.2 Generic even shell

For any weak core with p≥4, set k=2p+4, M=4p+8=2k and alpha index A=2p+4=k, also the midpoint label. The selected core arm ends with (3p+5,p+2,3p+7,p+3). The partner arm has pairs (2p+5+j,2p+3−j), j=0,…,p−1, followed by (3p+6,p,3p+8,p+1). Each arm has exactly k vertices; the endpoint-to-endpoint path is reverse(selected)||A||partner.

The vertex-label partition is explicit:

| Part | Low labels | High labels |
|---|---|---|
| Selected core | [0,p−1] | [3p+9,4p+8] |
| Selected tail | {p+2,p+3} | {3p+5,3p+7} |
| Partner prefix | [p+4,2p+3] | [2p+5,3p+4] |
| Partner tail | {p,p+1} | {3p+6,3p+8} |
| Midpoint | {2p+4} | empty |

These disjoint low sets partition [0,A] and high sets [A+1,M]. Alternation from the low midpoint ensures every edge crosses A. Its value k cannot be replaced by the odd-shell value k−1.

Selected center difference is 2p+1. Core differences are M minus the sum interval, namely [2p+10,M]. Its four tail edges, including the bridge from terminal low p−4, give 2p+9,2p+3,2p+5,2p+4. The partner prefix, including its center edge, gives [1,2p]; the four partner tail edges give 2p+2,2p+6,2p+8,2p+7. The eight tail values give 2p+{2,…,9}, and with the center difference and core interval partition [2p+1,M]. Thus every difference [1,M] occurs once.

The appended tails do not move any core position. Low offset zero remains ordinary zero at its actual depth; high offset zero becomes M at its actual depth. For compatible inputs these are a and a+1. The generic theorem preserves their individual positions even when an arbitrary weak core places them elsewhere.

## 4. Transfer to every actual spider

### 4.1 Center-zero residual for either parity

For every positive k, h≥0 and m≥0, let Q=hk+m. Label the residual center zero and arm i, 0≤i<h, by

```
b(i,2t+1)=(h−i)k−t,   0≤t<⌈k/2⌉;
b(i,2t)=ik+t,         1≤t≤⌊k/2⌋.
```

Leaves receive hk+1,…,Q. In block [ik+1,(i+1)k], even positions of arm i fill the first ⌊k/2⌋ values and odd positions of arm h−1−i fill the remainder. The center and these bands biject [0,Q]. Center edges give k,2k,…,hk; internal differences on arm i are |(h−2i)k−u|, 1≤u≤k−1. They fill open block index h−2i−1 if h−2i>0, and 2i−h otherwise. These two parity lists partition 0,…,h−1. Thus all nonmultiples and multiples of k through hk occur once; leaves complete [1,Q]. The proof includes h=0 and Q=0.

### 4.2 Index amalgamation and parity of the requested zero

Choose the requested long arm and a distinct partner, possible because n≥2. Put h=n−2 and identify the shell midpoint with the residual center. Retain path labels ≤A, add Q to path labels >A and add A to **all** residual labels. The bands [0,A], [A,A+Q], [A+Q+1,2k+Q] overlap only at the identified center label A and biject [0,N]. Residual differences remain [1,Q]; every path edge crosses A, so its difference increases by Q and fills [Q+1,N]. The resulting graph has exactly n k-edge arms and m center leaves.

In both parities the midpoint is low. Alternation places low zero only at even center depth; for a compatible pair, its high maximum is at odd outward depth a+1. If the requested depth is a, retain the transferred labeling. If it is a+1, complement the **entire completed spider** about N. This preserves all differences and places zero at that vertex. The final spider is not claimed to be alpha labeled. Bare-path complementation would change the index to k and midpoint to k+1 for odd k, or index to k−1 with midpoint k for even k; either breaks the required midpoint/index equality for the original graft.

This transfer is the alpha-amalgamation construction attributed to Huang–Kotzig–Rosa (1982), as precisely restated in Panpa–Imnang–Wasuanankul, Theorem 2.5 and its proof paragraph, and Shan–Zhong, Lemma 1. The original 1982 proof was not inspected here; attribution is mediated by those accessible later primary sources [Panpa2025; ShanZhong2026]. No new general gluing theorem is claimed.

## 5. Parity seam, thresholds and quantitative limit

For odd k≥35 set p=(k−3)/2. Then p≥16 and ⌊(p−16)/9⌋=⌊(k−35)/18⌋. Section 2 supplies the prefix and the odd shell transfers it. For even k≥36 set p=(k−4)/2; then ⌊(p−16)/9⌋=⌊(k−36)/18⌋=⌊(k−35)/18⌋. The equality holds because k−36 has an even residue in {0,2,…,16} modulo 18; adding one does not cross an 18-boundary. The same cores and even shell give the same displayed prefix. At odd k=19,…,33 and even k=20,…,34, p≥8 and the older small cores give depths 2–11. Every integer k≥19 is covered.

| Integer lengths k | Covered depths |
|---|---|
| 19,…,34 | 2,…,11 |
| 35,…,52 | 2,…,27 |
| 53,…,70 | 2,…,41 |
| 71,…,88 | 2,…,57 |

H is strictly increasing and unbounded, so u(d) exists. Since H(0)=27, u=0 for 12≤d≤27. For d≥28, write d−28=30q+r, 0≤r<30; then u=2q+1 for r≤13 and u=2q+2 otherwise. Because J_0,…,J_U overlap and begin at 12, every d≥12 with d≤H(U) is already in their union. The residue argument supplies its required core at the target p. Thus for d≥12, k≥K5(d) is equivalent to d≤D5(k); smaller depths use K5=19. This proves the threshold form with the same quantifiers.

For k≥35 write k=35+18U+r, 0≤r≤17. Then D5=27+15U−(U mod 2), so

```
5k−6D5(k)=13+5r+6(U mod 2) ∈ [13,104].
```

For 19≤k≤34 it is 5k−66∈[29,104]. Therefore the global deficit lies in [0,104]. Also D5≤27+15U<35+18U≤k in the upper branch, and D5=11<k in the lower branch. Dividing by 6k gives

```
0≤5/6−D5(k)/k≤104/(6k),
```

which proves the stated limit through all integer lengths. This improves the finite bound relative to the earlier odd prefix; it does not improve the limiting fraction. The older B+ moving interval had width fraction 11/18 and upper-endpoint ratio 5/6. Compatible seeds and depth-preserving closure fill a contiguous prefix to that reach.

## 6. Reverse-complement tracking and the 8/9 prefix

### 6.1 The involution and its classical representation

Let C be a balanced size-p core with the weak contract of Section 2. Define

```
T_p(C)[i]=p−1−C[2p−1−i],    0≤i<2p,
```

and tag the target anew H,L starting H. Reversal exchanges the source tag sides because 2p−1 is odd. Offset complementation permutes [0,p−1] on each side; adjacent sums s map to 2p−2−s. The endpoints become p−1−(p−4)=3 and p−1−3=p−4. Thus the weak shell contract is preserved, and applying T_p twice returns C.

The unique sum 2p−2 forces H(p−1),L(p−1) adjacent. If their first zero-based index is t, reflection turns them into zeros at one-based depths b=2p−1−t and b+1=2p−t. Their order may be L0,H0 or H0,L0. T_p need not preserve H4,L0,H0,L1; consequently all insertions requiring that neighborhood are completed **before** reflection.

The operation is a composition of classical alpha-label transformations, not a new general symmetry. Encode the ordinary alpha path by F(C)_i=2p−1−C_i for even i and F(C)_i=C_i for odd i, with q=2p−1 and alpha index A=p−1. Write K(x)=q−x for global complement and I_A(x)=A−x for x≤A, I_A(x)=q+A+1−x for x>A. Direct substitution yields

```
F(T_p(C))_i=(K∘I_A)(F(C)_(2p−1−i)).
```

Barrientos describes complement and inverse/reverse alpha labeling explicitly on printed p.302 [Barrientos2020]. The new positional argument below tracks the opposite extreme pair under this classical composition; its historical priority remains unresolved.

### 6.2 Track the maximum pair through the existing gadgets

Use a compatible input core whose maximum pair is entirely before its old low zero L0. A size-q insertion shifts all old positive entries by q. The old maximum p−1 becomes p+q−1 and exceeds every newly inserted value in [1,q], so its pair stays adjacent and remains the unique maximum pair. Since the replacement chains are placed at the later zero neighborhood, only prefix P changes this earlier pair's index: t becomes t+len(P). It remains before the zero pair, permitting iteration.

The first reflected zero depth therefore advances by

```
[2(p+q)−1−(t+len(P))]−[2p−1−t]=2q−len(P).
```

Use only the q9 gadgets of Appendix D with old zero displacement 4 and 6. Their prefix lengths are 2 and 4, so their **reflected** displacements are 16 and 14. Their inserted side sets [1,9] and replacement-chain sums [1,19]∪{22}, together with retained sums {0}∪([20,2p+16]\{22}), prove universal validity exactly as in Section 2. No new gadget search is a premise.

For j insertions, let s of them have prefix length 2 and j−s prefix length 4. Every s=0,…,j is allowed, in any order; the reflected pair occupies b+14j+2s and the following depth. Their union is the complete depth interval

```
[b+14j,b+16j+1].
```

This works for either parity of b. It is a depth interval containing both vertices of each pair, not an interval of pair starts requiring another +1.

### 6.3 Six exact source seeds and orientation

The six selected arrays are exact rows of Appendix C, reproduced with their hashes in Appendix E. No new seed existence claim is needed.

| p0 | Original low-zero depth | Original maximum depths | Reflected zero-pair depths | Reflected order |
|---:|---:|---|---|---|
| 16 | 16 | 6,7 | 26,27 | L0,H0 |
| 17 | 22 | 8,9 | 26,27 | L0,H0 |
| 18 | 22 | 10,11 | 26,27 | L0,H0 |
| 19 | 20 | 12,13 | 26,27 | L0,H0 |
| 20 | 24 | 16,17 | 24,25 | L0,H0 |
| 21 | 22 | 15,16 | 27,28 | H0,L0 |

Every original maximum pair precedes the old zero pair. Intersect the six full intervals from Section 6.2. The largest lower endpoint comes from b=27 and the smallest upper endpoint from b=24, giving, for j≥1,

```
I_j=[27+14j,25+16j].
```

This is nonempty because its upper minus lower is 2j−2. In particular I_1={41} and I_2=[55,57]. Adding another one to the common upper endpoint would be incorrect.

For p≥16+9j divide p−(16+9j)=6r+δ, 0≤δ≤5. Choose the seed of size p0=16+δ, perform j compatible insertions, reflect at size p0+9j, and **then** append r translated C6 blocks. Sections 2.2–2.3 prove the endpoint, side and sum contract throughout; the appended positive entries leave both new zeros and their indices unchanged. Reflection and append are not interchanged: appending first changes which maximum pair is turned into zeros. Every depth in I_j is therefore available at every target p≥16+9j, with all residues covered.

### 6.4 Join D5 and transfer either pair orientation

For p≥25 set U=⌊(p−16)/9⌋≥1. The accepted D5 prefix ends at F(U)=27+14U+2⌊U/2⌋. At that same target size I_U begins at 27+14U, so it overlaps the prefix. Its upper endpoint exceeds F(U) by

```
2U−2⌊U/2⌋−2=U+(U mod 2)−2≥0.
```

Thus their union is [2,25+16U]. For p<25 the inherited D5 branches give the two initial constant prefixes. The generic shells of Section 3 apply to every reflected weak core; they require no retained compatible neighborhood or fixed orientation. Both parities give U=⌊(k−35)/18⌋ as in Section 5, with p≥25 exactly at odd k≥53 and even k≥54. The two initial branches cover every k=19,…,52. This proves the all-integer D6 prefix without a seam gap.

Low zero remains at an even center depth; high maximum is at its adjacent odd depth, with either inward or outward order. In the p21 reflected row, H0,L0 at depths 27,28 gives maximum at odd depth 27 **inward of** zero at even depth 28. All reflected shifts are even, so this orientation persists after insertions and append. To request either position, apply the actual-spider graft of Section 4 and complement the entire graph precisely when the target is H0. The maximum need not be the outward neighbor of the low zero. An always-outward premise applies only to the original compatible seed bank, not to these reflected rows.

D6 agrees with D5 at U=0,1,2 and first strictly improves it at U=3: k=89,90 have D5=71 and D6=73. The gain for U≥1 is U+(U mod 2)−2. This comparison concerns the frozen project bounds, not worldwide priority.

### 6.5 Exact deficit, legal depths and inverse threshold

For k≥53 write k=35+18U+r, 0≤r≤17. Then

```
8k−9D6(k)=8(35+18U+r)−9(25+16U)=55+8r∈[55,191].
```

For k=19,…,34 the deficit is 8k−99∈[53,173], and for k=35,…,52 it is 8k−243∈[37,173]. The global bound is therefore 0≤8k−9D6(k)≤191. It proves D6(k)<k and

```
0≤8/9−D6(k)/k≤191/(9k),
```

hence the limit 8/9 through all integers, an increase of 1/18 over 5/6. For d≥28 the first integer U whose 25+16U reaches d is ⌈(d−25)/16⌉≥1; the first length of that block is 35+18U. The earlier constant branches yield K6=19 for depths 2–11 and K6=35 for depths 12–27. Thus the stated sufficient K6 thresholds are exactly the inverse of D6's coverage function. No optimality or full near-tip assertion follows.

## 7. The global q11 prefix and a core-level induction

### 7.1 A universal q11 step before reflection

Use the same six tracked seeds and b=(26,26,26,26,24,27) from Section 6. The additional exact size-eleven gadget is

```
P=(3,8);
B=(11,10,5,5,4,2,3,4);
D=(1,1,2,6,6,7,7,9,10,8,9,11).
```

With the established tags, its new H side and new L side each permute [1,11]. The three replacement chains P,H14; H15,B,L0; H0,D,L12 give sums [1,23]∪{26}. The retained sums are {0}∪([24,2p+20]\{26}). These disjoint sets partition [0,2(p+11)−2]. Old positive offsets increase by 11, old zeros stay zero, endpoints become H3,L(p+7), and H4,L0,H0,L1 persists. The maximum pair remains before the window, with first index shifted by len(P)=2. The reflected depth gain is therefore 2q−len(P)=22−2=20. This universal identity has its own frozen separate gadget GO; that local verdict alone does not establish global coverage.

For target p≥16 and nonnegative q11 count a and q9 count j satisfying 11a+9j≤p−16, let

```
δ=(p−16−11a−9j) mod 6;
h=(p−16−11a−9j−δ)/6.
```

Choose seed size 16+δ. Perform all a q11 and j q9 insertions while the input is compatible, reflect once, and then append h translated C6 blocks. With s of the q9 steps using prefix length 2 and j−s using length 4, the pair depths are b_δ+20a+14j+2s and the following integer. Their attainable union, as 0≤s≤j, is the full depth interval

```
I(p;a,j)=[b_δ+20a+14j,b_δ+20a+16j+1].
```

This includes both pair orientations, and its upper endpoint already includes the second member. It receives no extra +1. The insertion word's order does not affect size or tracked depths, because the maximum pair stays before the window throughout. C6 is appended only after reflection; a q11 count added to a recipe is compiled before reflection, never inserted into an already reflected weak core.

### 7.2 Exact finite bridges followed by unbounded induction

Appendix F gives six starting rows p=61,…,66 and eleven bridge rows p=67,…,77, with every recipe, exact interval and endpoint. All listed recipes have h=0 and are directly verified from the preceding formula. At each starting size the accepted D6 **core** construction supplies depths 90,…,105: the D5 compatible-core prefix reaches 101 and the reflected q9 interval supplies 97,…,105. The starting chains extend this through F(p). Thus every base p=61,…,66 has endpoint-compatible cores for every depth 90,…,F(p).

For p=67,…,77 the listed chains cover [F(p−6)+1,F(p)]. Every p≥67 is uniquely p0+11t with p0∈{67,…,77}, t≥0. Add t q11 insertions to each recipe before reflection. Size increases by 11t and the entire depth interval by 20t. Since F(x+11)=F(x)+20 for x≥61, these translated recipes cover [F(p−6)+1,F(p)] at every p≥67.

Induct by six on p. At p≥67, append one C6 to the already constructed weak cores at p−6. This preserves all depths 90,…,F(p−6). The translated bridge fills every remaining depth through F(p). The six bases establish the induction for all p≥61. This is a statement about actual **cores** with the shell contract, not an attempt to append to arbitrary inherited spider labelings. At every such p, D6 covers at least through depth 105. Its lower prefix therefore overlaps the new core interval and supplies depths 2,…,89. Applying the two generic shells and the complete-spider transfer gives the full D7 prefix for both parities.

The separate auditor also reconstructs the result through a different induction. Its 371 positive core certificates supply depths 83,…,F(p) at eleven base sizes p=61,…,71. For p≥72, C6 from p−6 supplies 83,…,F(p−6), while adding q11 before reflection to recipes at p−11 supplies 103,…,F(p), since F(p)=F(p−11)+20. The intervals overlap because F(p−6)≥F(66)=115. Both predecessors are smaller and at least 61. This confirms the unbounded core statement without relying on completeness of the algorithm that discovered those finite positive certificates.

### 7.3 Parity, nonregression and quantitative bound

For odd k=2p+3 and even k=2p+4, p=⌊(k−3)/2⌋. Thus p≥61 corresponds precisely to all k≥125, with no parity seam. All shell and graph arguments of Sections 3–4 apply to the weak cores. A low zero stays zero and a high target becomes nk+m; complement the entire graph for the latter. The reflected p21 maximum can be inward of the even zero, as in Section 6; no always-outward requirement is introduced.

The D6 core endpoint is at most F for p≥61. The 99 exact cases p=61,…,159 verify the inequality. Under p↦p+99, F increases by 180 and the D6 core endpoint by 176, so the difference increases by four. Those 99 residues prove nonregression for every p≥61. The first strict improvement is k=125,126: the D6 endpoint 105 becomes 107. This is a comparison with the project's sufficient bounds, not a historical novelty claim.

For k≥125 write p=61+11a+r and k=2p+3+ε, ε∈{0,1}. Then

```
10k−11F(p)=73+20r+10ε−44⌊min(r,9)/2⌋.
```

The eleven r values and two parities give deficits between 57 and 107. For k=19,…,34 the inherited deficit is 10k−121; for k=35,…,52 it is 10k−297. For k=53,…,124 write k=35+18U+t, 0≤t≤17 and 1≤U≤4: the deficit is 75+4U+10t, at most 261, attained at k=124. All branches are nonnegative. Hence the global bound is 0≤10k−11D7≤261. It implies legal depths and

```
0≤10/11−D7(k)/k≤261/(11k),
```

which proves the limit 10/11 through all integer lengths.

### 7.4 Why K7 is the inverse of this sufficient prefix

Below depth 90, the three K7 branches invert the inherited D6 plateaus up to its last pre-q11 endpoint 89 at k=124. For d≥90, the chosen a is the first nonnegative block index with d≤123+20a. Then s selects the first one of the five rising values 107+20a+4s, 0≤s≤4, reaching d. These values first occur at p=61+11a+2s, so their first odd length is 125+22a+4s. The same endpoint continues at the following even length. The plateau increments within a block are (0,0,4,4,8,8,12,12,16,16,16); the next block increases the base by 20. These explicit monotone plateaus prove D7(k)≥d exactly when k≥K7(d). The separate global audit verifies this inverse as well. The term “inverse” concerns D7's constructed bound only.

## 8. The q10 gap completion

### 8.1 Universal mixed insertion words

Use only the size16 and size17 source seeds of AppendixE. Both have reflected first pair depth26 and their original maximum pair lies before the compatible zero window. Add the accepted q10 gadget P=(3,8),B=(10,8,9,10,5,5,4,2,3,4),D=(1,1,2,6,6,7,7,9). Its new tagged sides each permute1..10 and replacement chains give sums[1,21]∪{24}. Retained sums are{0}∪([22,2p+18]\{24}); together they give the enlarged sum interval. Endpoints and H4,L0,H0,L1 persist exactly as in Sections2 and7.

All three q9/q10/q11 gadgets used here have prefix length2. Their old maximum-pair first index therefore increases by2 and their reflected depth gains are16,18,20. For seed size s∈{16,17}, counts(c,b,a) give size p=s+9c+10b+11a and consecutive reflected depths26+16c+18b+20a and27+16c+18b+20a. Perform the entire mixed word while the core is compatible, then reflect once. This D8 gap proof needs no C6 append; the older D7 proof retains its separate post-reflection C6 steps. No insertion into an already reflected core is assumed.

### 8.2 Seven exact recipes, including both halves of the r10 gap

| p | Seed size | q9 | q10 | q11 | Depths |
|---:|---:|---:|---:|---:|---|
|62|16|4|1|0|108,109|
|64|16|3|1|1|112,113|
|66|16|2|1|2|116,117|
|68|16|1|1|3|120,121|
|70|16|0|1|4|124,125|
|71|17|0|1|4|124,125|
|71|16|0|0|5|126,127|

For p=61+11a+r, subtract the predecessor F7=107+20a+4⌊min(r,9)/2⌋ from F8. The eleven gains are(0,2,0,2,0,2,0,2,0,2,4). Thus base residues r0,2,4,6,8 need no extra depths. Rows at p62,64,66,68,70 supply the five two-depth gaps. At p71,r10, F7=123 and F8=127: the size17 recipe gives124/125 and the size16 recipe126/127. The top pair alone would leave two depths missing and does not prove a contiguous prefix.

For any p≥61 write p=p0+11t with p0∈{61,…,71},t≥0. Add t q11 insertions before reflection to the applicable finite recipes. Size rises by11t and both depths by20t; both F7 and F8 rise by20t. The translated rows therefore fill every integer in[F7(p)+1,F8(p)]. The accepted D7 prefix supplies the lower part. This proves complete coverage through F8 unboundedly, without search completeness or a new induction on arbitrary spider labelings.

### 8.3 Actual spiders, joins and deficit

The reflected cores retain the weak contract, so the odd/even shells and residual index graft of Sections3–4 apply. Add A to all residual labels, retain low shell labels and add Q to high shell labels. L0 stays zero and H0 becomes N=nk+m; complement the entire spider when H0 is requested. The new seven rows have L0,H0 order, but the generic transfer and inherited D7 coverage also permit H0,L0. The same p=⌊(k−3)/2⌋ covers odd k=2p+3 and even k=2p+4. Any requested arm has a distinct partner because n≥2, including empty residual cases.

Within a size block F8 grows by2 per p, and its value at r10 equals the next block's r0 value. It is nondecreasing and matches D7 at p61. Its first strict gain is k127/128,107→109; at k145/146 it is123→127. The gains recur after k↦k+22 with both endpoints rising by20. For k=2p+3+ε,ε∈{0,1},

```
10k−11D8(k)=73−2r+10ε,    k≥125.
```

The upper-branch deficit lies in[53,83]. The inherited lower branch retains maximal deficit261 at k124. Hence globally0≤10k−11D8≤261, D8<k and0≤10/11−D8(k)/k≤261/(11k). This proves the unchanged all-integer limit10/11. The improvement adds bounded depths at infinitely many lengths; it does not increase the limiting fraction or establish a graph-theoretic optimum.
## 9. Verification and methods
The new [D8 formal author](research-audits/graceful-q10-gap-fill-formal-2026-10-09-a/report.md) and [separate copied-source replay](research-audits/graceful-q10-gap-fill-lean-replay-2026-10-09-a/audit-report.md) bind `GracefulBoundary.GapFill.all_lengths_prefix_zero` on the actual indexed SpiderVertex/spiderGraph, for every k≥19,n≥2,m≥0,selected arm and depth2..D8(k). The final theorem has no supplied core, parity, residual or transfer hypothesis. The replay rebuilt all57 modules and reconciled all706 named theorem axiom reports, with only propext,Classical.choice and Quot.sound. It confirms universal q10/core tracking, all seven recipes including both p71 pairs, unbounded q11 translation,D8≥D7,monotonicity,legal depths,the global261 deficit and integer precision criterion. The author index SHA-256 is `a5aaf2d94b7eb81198f7a16e8e84b30cf21bf9e40259075ec94d195183d83619`; the replay report is `692f33bc1a14ebc237d246f5fc1bd8bc63e46d97e5e5a042c0469b3475e46dbd` and replay index `3787f77fc7ef1a09282cb65d7b9e2765d12ddef7ce6b0cab3730d302dd492d2a`. Both indexes identify SHA256SUMS.txt, not JSON manifests. The author's replay-pending-at-freeze note remains historical. Correctness is relative to the recorded Lean4.34.0 kernel/compiler,Std,indexed graph model and those standard axioms. K8 inverse/minimality,recipe-family maximality and a Lean Real/Tendsto equivalence are outside this package. The integer criterion uses cutoff262*precision+19.


The [separate D8 mathematical audit](research-audits/graceful-q10-gap-fill-independent-2026-10-09-a/report.md) reports **GO** for the exact theorem, seven recipes and unbounded translation, all n,m,arms and both parities, the r10 join, monotonicity, deficit261 and limit10/11. Report SHA-256 is `b9886f996b045aea344b4f62d3f6344801fa481024d943283b2fe5a7456f5c15`; manifest is `42e6eb15ccb557b6f81b5addd1db2cd69ee5c394d42b50356a66422e5272e262`. The bound [author report](research-audits/graceful-q10-gap-fill-beyond-d7-2026-10-09-a/report.md), SHA-256 `3150df1b1f6296c580eebf5c2bc4b7bba9b6ae97436b0ebfbb821f70c41658a6`, retains its earlier pending-at-freeze note; author manifest is `ce41485e485b6dd86c92092923326fdaa47095fa8243eb4d733c4531d5d5b685`. The separate audit verifies4,500 actual BFS spiders and universal partitions without importing author source. These finite diagnostics support the symbolic proof. **D8 formal author and separate copied-source Lean replay are GO for their exact scope.** No external review or priority determination is supplied by this mathematical GO.


The [separate global D7 mathematical audit](research-audits/graceful-ten-elevenths-independent-2026-10-09-a/report.md) now reports **GO** for the exact all-integer theorem, nonregression, deficit 261 and K7 inverse. Report SHA-256 is `60a958449111a6f875be84a05d419c94c474db0cb770b3c07af799f57633c1cf`; manifest SHA-256 is `4fd38e5e2b60ed6873105ffa751b5922a87a6a12f137956abf19e289f343c24a`. The [bound author report](research-audits/graceful-ten-elevenths-global-2026-10-09-a/report.md), SHA-256 `bf7eec616fa42a5465703e4f90d296f02dcb35a0b91c5c6c82bdfcf5208f9249`, retains its earlier pending-at-freeze statement; its manifest is `419634baa520139e83395fb2014478710317d8bf72f83c4c7c54e31083be739d`. The q11 gadget's separate acceptance is bound to report `f90b3ef57a1f9d9f762f99a2db7b68eef8d88c1862e35809794122e54be33a44` and manifest `720ef06b23bf2a7a5cc39dd02d260f519ac0939ad58e69be73f747ebe1ef4afd`. The global audit reconstructs positive core certificates, an unbounded recipe induction and 19,864 actual-spider BFS checks without importing author code. Finite tests supplement the proof; they are not its infinite premise. The [D7 formal author package](research-audits/graceful-ten-elevenths-formal-2026-10-09-a/report.md) and [separate D7 copied-source replay](research-audits/graceful-ten-elevenths-lean-replay-2026-10-09-a/audit-report.md) now both report GO for the exact actual-spider D7 prefix, q11/core construction, K7 inverse, nonregression, monotonicity and integer ratio criterion. The formal author checksum index is `76022dcd140c9a989040d7c25e8ed597336d0971739066ad95e7983c129bdcec`; the replay report is `8d5bfa6d79328bd2c253fbdf5f1f49c053438d56d12936ae07b7b1f810e55e25` and replay index `ec07e893a6760470f90c9e3afc70b23c827efbab40d75f110b1c3b32d76912a1`. Each index identifies SHA256SUMS.txt, not a JSON manifest. The author report preserves its historical replay-pending-at-freeze note. These packages do not formalize D8.

The [separate D6 mathematical audit](research-audits/graceful-reverse-complement-independent-2026-10-09-a/report.md), report SHA-256 `d018ad8ffba50cf53a6d1f78e34df406285985a9b4c58098f485773a9ed4c7d6`, gives **GO** for the exact reflected-pair theorem, all residues and both orientations, D5 union, both shells, deficit 191 and 8/9 limit. Its manifest SHA-256 is `9ed595d251da038abb9544ae1e0387580ed1df3d334c992d2368989e23a0ef54`. The bound [author report](research-audits/graceful-beyond-five-sixths-block-principle-2026-10-09-a/report.md), SHA-256 `680c39948d7562214de814052eda2bf0bf1b59fa642a757e33c7a4cd82a4014e`, retains its historical pending-at-freeze note. The audit additionally proves K6. It reconstructs insertion as tagged graphs without importing author code or a solver, checks actual spider labels/edges and BFS depths, and diagnoses false assumptions about pair order and append-before-reflect. The [D6 formal author](verification-scope.md#source-records) and [separate D6 replay](verification-scope.md#source-records) are both GO for the exact all-integer D6 prefix, K6, reverse-complement tracking and integer ratio criterion. The author checksum index is `2f7d49ce7758a9834b212addd031ebd2d3bc2c16a8c03064afc44d4171f254f1`; the replay index is `e1bbec50ee38d89766a1c3b0801b5bea9f99a548afe85940779cbd06bae0f090`. The original author replay-pending note is historical. D6 and D7 formal limits remain integer precision criteria rather than Lean Real/Tendsto statements; neither package supplies formal verification of D8.

| Mathematical statement | Bound internal evidence | Formal scope |
|---|---|---|
| Compatible 48-core prefix | Author report and separate compatible-prefix audit GO | Complete D5 formal author and separate replay GO |
| Universal even shell and transfer | Even-shell author and separate audit GO | Complete D5 formal author and separate replay GO |
| Unified all-integer D5/K5 and deficit 104 | Final combination acceptance GO, bound to compatible/even/older inputs | Complete D5 formal author and separate replay GO |
| Older odd v4 prefix | Formal author GO and copied-source replay GO | Exact older threshold/prefix and integer convergence criterion |

The compatible audit reconstructs literal cores, universal gadgets and actual spiders using its own tagged-graph implementation and BFS. The even audit proves the generic shell against the same weak contract. Their composition is justified by matching that contract, not by upgrading the even audit's earlier conditional bank note. The final combination report supplies the parity seam and quantitative arithmetic. Immutable author reports retain their original pending-at-freeze wording; later audit reports carry the acceptance statuses. Source hashes and exact report links are listed in the README.

The older v4 Lean replay rebuilt 34 modules and reconciled 428 theorem axiom reports. Its checksum index is `27d528038e6a0b782af9d7aef4b9be722e6fa99ad6f18c083373fbc4b687b9a5`. Dependency union is confined to propext, Classical.choice and Quot.sound with the recorded Lean 4.34.0/Std toolchain. Its ratio result is an integer reciprocal-precision criterion, not a Lean Real/Tendsto theorem. That replay does not formalize the new compatible bank, generic even shell or deficit 104. The [complete D5 formal author package](verification-scope.md#source-records) and its [separate copied-source replay](verification-scope.md#source-records) now both report **GO** for the exact all-integer threshold/prefix, generic even shell, actual-spider transfer, deficit 104 and integer convergence criterion. All 42 modules were freshly compiled and all 555 named theorem axiom reports reconciled. The dependency union remains the three standard axioms with Lean 4.34.0/Std. The author checksum index is `edab06852d066c34b5e52cfae078dfc892bbcf793a4b50c24519d3de06f78c0d`; the replay index is `29f42b26363ce54e4605686f49b4863de89cd0ff53eee24a94eb6382a5014f2f`. Both identify `SHA256SUMS.txt`, not JSON manifests. Formal ratio scope is still the integer reciprocal-precision criterion; no Lean Real/Tendsto theorem is claimed.

Jordi Gartner owns and publishes this work through Beedbyte. AI tools assisted the documented finite-core construction, tracked-pair and core-induction reconstruction, exact arithmetic and graph checker implementation, symbolic proof development, and separate internal checks in the named packages; bound formal records document assisted Lean proof development and compilation. These are specific methods records. Internal project checks do not constitute external review or scholarly peer review.

## 10. Prior work and open historical questions

D8 adds a finite residue-gap completion to the accepted D7 construction. Its exact global mathematical GO is distinct from the earlier gadget and D7 verdicts. Reflection and index amalgamation remain classical; historical novelty and general older-method subsumption remain UNKNOWN. No external review is recorded.



The q11 step and its global interval induction are a further project-level consequence of the bound compatible cores, tracked-pair transformations and generic shells. The retained 8/9 primary comparison concerns D6, not the new global D7 theorem; it supplies classical-operation attribution and bounded background rather than a new D7 priority assessment. Reflection is still the classical composition described in Section 6.1. Historical novelty and general equivalence to older constructions remain UNKNOWN. No external specialist review or scholarly peer review is recorded.

Path prescribed-zero results and the centrally leafed path of Luiz–Campos–Richter already cover complete n=2,m=0 and n=2,m=1 subfamilies, for both parities [LuizCamposRichter2017]. Center-zero equal-arm gracefulness and classical graft mechanisms are older ingredients; ordinary gracefulness alone does not prescribe an internal zero.

Kotzig's balanced endpoint feasibility, restated in Ollis Lemma 5.5, overlaps H3/L(p−4) endpoints after mapping Hh↦2p−1−h,Ll↦l and reversal. Endpoint feasibility alone does not prescribe the H4,L0,H0,L1 window or its position. Balanced insertion and more elaborate older pi representations may have further consequences; parameter equivalence has not been exhausted [Ollis2020].

The frozen joint-anchor comparison correctly distinguishes one-vertex path existence from a single alpha witness with index and midpoint A, even zero anchor a and outward maximum at a+1. For odd k, A=k−1; for even k, A=k. A maximum edge forces adjacency but not its direction. Separate existence witnesses cannot be combined without proof. An older argument could nevertheless subsume the spider conclusion without this stronger certificate.

The latest bound primary comparison, report SHA-256 `a799b85dff67941a2c1ddb0575a1848e88bded8d7672708025b357c6011a56bb`, covers the compatible bank, even shell and final D5 combination. The concrete remaining questions are whether older Cattell/Kotzig/Rosa path machinery supplies these joint anchors and explicit prefix thresholds, and whether existing insertion operations transform into the bound core extensions. Original Cattell, Kotzig/Rosa and 1982 proofs remain insufficiently inspected; later primary restatements mediate attribution. **Historical priority, worldwide novelty and general non-subsumption remain UNKNOWN.** Neither stronger bounds relative to previous Beedbyte versions nor internal GO decisions establish priority.

The [frozen 8/9 primary comparison](verification-scope.md#source-records), report SHA-256 `ae1f33d62f63219e745218e1219d3f8950444bb7c16c52b1c84ced3c5064d7b2`, establishes the exact classical decomposition of T_p in ordinary alpha-path coordinates and records the D6 audit GO separately. It does not establish historical non-subsumption of the complete tracked-pair theorem. The corrected specialist question now allows the adjacent odd maximum inward or outward of the even zero, as specified by each certificate, and asks whether older constructions supply the full tracked-pair/position/rate contract or otherwise subsume the all-n,m prefix. The unread original Cattell/Kotzig/Rosa machinery remains material. An always-outward path premise would omit the p21 reflected residue and is not the D6 target.
## References

- **[Barrientos2020]** Christian Barrientos, *Alpha graphs with different pendent paths*, Electronic Journal of Graph Theory and Applications 8(2) (2020), 301–317. [Publisher PDF](https://www.ejgta.org/index.php/ejgta/article/download/1036/pdf_143), DOI 10.5614/ejgta.2020.8.2.8. Complement and inverse/reverse alpha transformations, printed p.302.

- **[Ollis2020]** M. A. Ollis, *Sequences in dihedral groups with distinct partial products*, Australasian Journal of Combinatorics 78(1) (2020), 35–60. [Publisher PDF](https://ajc.maths.uq.edu.au/pdf/78/ajc_v78_p035.pdf). Lemma 5.5 and Theorem 5.6, pp.53–54.
- **[LuizCamposRichter2017]** Atílio G. Luiz, C. N. Campos and R. Bruce Richter, *Some families of 0-rotatable graceful caterpillars*, IC-17-12, Universidade Estadual de Campinas, 4 August 2017. [Institutional PDF](https://ic.unicamp.br/~reltech/2017/17-12.pdf). Lemma 4 and Theorem 14.
- **[Patterson2017]** Patterson, *New Classes of Graceful Spiders and Related Computational Results*, master's thesis, Ball State University, May 2017. [Institutional text](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content). Alpha amalgamation and Theorem 5.3.6; broader Conjecture 5.4.4 is not a theorem. The fresh full-text retrieval in the earlier draft returned 403; retained primary-reading records support the cited loci.
- **[HuangKotzigRosa1982]** C. Huang, A. Kotzig and A. Rosa, *Further results on tree labelings*, Utilitas Mathematica 21 (1982), 31–48. Attribution and graft statement are mediated by [Panpa2025] and [ShanZhong2026]; original proof not inspected here.
- **[Panpa2025]** A. Panpa, S. Imnang and T. Wasuanankul, *Graceful Labeling of Spider Graphs With at Most Five Legs*, Journal of Applied Mathematics (2025), article 5826777. [Publisher full text](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777). Theorem 2.5 and following proof paragraph.
- **[ShanZhong2026]** Songling Shan and Yucheng Zhong, *Graceful Labeling of Two Families of Spiders*, [arXiv:2605.14295v2](https://arxiv.org/html/2605.14295v2), version tagged 15 May 2026. Lemmas 1–2. The retrieved HTML also carries an August 24, 2026 heading; the exact version URL identifies the cited text.

## Certificate appendices

Appendices A and B below preserve the exact earlier v5 tables. Appendix C adds the complete 48 compatible cores; Appendix D supplies the seven universal gadget blocks. Canonical row hashes identify UTF-8 compact JSON numeric arrays without spaces, BOM or final newline. These certificates are mathematical inputs, not solver verdicts.

## Appendix A. Exact balanced-core certificates

Entries in each following row have tags H,L,H,L,… in the displayed order. The depth pair is one-based from the selected center, after shell construction. Each row satisfies the side-permutation, sum-permutation and H3/L(p−4) endpoint contract in Section 4.1.

| Family | p | Zero depths | Ordered numeric entries |
|---|---:|---|---|
| Theorem 2 | 6 | 2/3 | 3,0,0,1,1,3,2,4,4,5,5,2 |
| Theorem 2 | 6 | 3/4 | 3,1,0,0,2,3,4,4,5,5,1,2 |
| Theorem 2 | 6 | 4/5 | 3,1,1,0,0,3,2,4,4,5,5,2 |
| Theorem 2 | 6 | 5/6 | 3,5,5,4,0,0,1,1,2,3,4,2 |
| Theorem 2 | 6 | 6/7 | 3,3,2,1,1,0,0,4,4,5,5,2 |
| Theorem 2 | 6 | 7/8 | 3,3,4,4,5,5,0,0,1,1,2,2 |
| Theorem 2 | 6 | 8/9 | 3,3,2,5,5,4,4,0,0,1,1,2 |
| Theorem 2 | 6 | 10/11 | 3,1,2,3,4,4,5,5,1,0,0,2 |
| Theorem 2 | 9 | 2/3 | 3,0,0,1,1,3,2,4,4,6,7,2,5,7,8,8,6,5 |
| Theorem 2 | 9 | 3/4 | 3,1,0,0,2,3,4,2,1,7,6,4,5,6,8,8,7,5 |
| Theorem 2 | 9 | 4/5 | 3,1,1,0,0,3,2,4,4,6,7,2,5,7,8,8,6,5 |
| Theorem 2 | 9 | 5/6 | 3,2,1,1,0,0,4,3,5,4,2,8,8,7,7,6,6,5 |
| Theorem 2 | 9 | 6/7 | 3,1,2,4,1,0,0,2,5,3,6,6,4,7,7,8,8,5 |
| Theorem 2 | 9 | 7/8 | 3,1,2,3,4,2,0,0,1,7,6,4,5,6,8,8,7,5 |
| Theorem 2 | 9 | 8/9 | 3,1,2,3,6,6,1,0,0,2,4,4,7,7,8,8,5,5 |
| Theorem 2 | 9 | 10/11 | 3,1,2,3,5,4,6,6,1,0,0,2,4,7,7,8,8,5 |
| Theorem 3 | 12 | 12/13 | 3,3,1,2,5,4,6,5,7,6,2,0,0,1,4,10,9,7,8,9,11,11,10,8 |
| Theorem 3 | 12 | 14/15 | 3,3,1,2,7,10,11,11,9,7,8,5,2,0,0,1,4,4,6,6,5,9,10,8 |
| Theorem 3 | 12 | 16/17 | 3,3,1,2,8,6,7,11,11,10,10,9,6,5,2,0,0,1,4,4,5,7,9,8 |
| Theorem 3 | 12 | 18/19 | 3,3,1,2,8,9,10,10,11,11,7,7,9,6,6,5,2,0,0,1,4,4,5,8 |
| Theorem 3 | 12 | 20/21 | 3,2,1,3,7,9,9,6,5,7,10,10,11,11,8,5,4,4,2,0,0,1,6,8 |
| Theorem 3 | 12 | 21/22 | 3,6,7,9,11,11,10,7,8,10,9,5,6,4,2,3,5,2,1,1,0,0,4,8 |
| Theorem 3 | 15 | 12/13 | 3,5,8,13,14,14,12,10,7,4,2,0,0,1,4,6,9,7,5,2,1,3,6,8,10,9,11,12,13,11 |
| Theorem 3 | 15 | 14/15 | 3,6,6,7,11,8,7,9,8,3,4,4,1,0,0,2,2,1,5,5,9,13,14,14,12,12,13,10,10,11 |
| Theorem 3 | 15 | 16/17 | 3,5,11,12,13,13,14,14,10,9,12,10,8,6,4,0,0,1,1,2,5,7,6,3,2,4,7,8,9,11 |
| Theorem 3 | 15 | 18/19 | 3,5,7,10,14,14,13,13,12,9,10,8,5,4,6,1,1,0,0,3,2,2,4,7,9,6,8,12,11,11 |
| Theorem 3 | 15 | 20/21 | 3,3,1,2,6,9,10,10,13,14,14,12,12,13,8,8,9,5,2,0,0,1,4,6,7,4,5,7,11,11 |
| Theorem 3 | 15 | 22/23 | 3,3,1,2,5,5,11,13,12,9,10,12,14,14,13,10,8,6,6,7,2,0,0,1,4,4,7,8,9,11 |

## Appendix B. Thirty exact all-residue small-depth cores

Each row has alternating tags H,L beginning H. The pair lists the one-based positions of L0,H0. SHA-256 is over the UTF-8 compact JSON numeric array, with no spaces, BOM or final newline. These row hashes identify literals; the full seed-file hash is separately bound in source-hashes.json.

| p0 | Zero depths | Exact core | Compact-array SHA-256 |
|---:|---|---|---|
| 8 | 2/3 | 3,0,0,1,1,6,5,5,7,7,6,3,2,2,4,4 | `a3c88261b1896c3129a22e87e8199bf0cc172d6239d8338d30e7a347ce25f3a8` |
| 8 | 4/5 | 3,3,5,0,0,1,1,2,2,5,4,6,6,7,7,4 | `cf933a566c3ba3acd30f97baba80b059d0e51b12b33472f668aa64232a3f7c09` |
| 8 | 6/7 | 3,3,5,6,1,0,0,2,2,1,4,5,7,7,6,4 | `09ca1fcd381c90a0f3100c12d35c22f09f5b6295372ed23f36aaf82e97c22deb` |
| 8 | 8/9 | 3,5,2,2,4,1,1,0,0,3,7,7,6,6,5,4 | `c958fc4f51092a509a5c0c9e427e5e7a122bd008f21b7dce94505613e2fd65ee` |
| 8 | 10/11 | 3,1,2,3,5,7,7,6,1,0,0,2,4,5,6,4 | `444626e80ee1d8efd88301d56d23d81ff85b4fb296efdfe23a745adc2c5babed` |
| 9 | 2/3 | 3,0,0,1,1,3,2,6,8,8,7,4,6,7,5,2,4,5 | `845f73bbb32726dbb2456e95c1ab1164ba759f2ba7fafa739375f372f65241f8` |
| 9 | 4/5 | 3,1,1,0,0,3,2,7,8,8,6,6,7,4,4,2,5,5 | `df3dba3a8623d926681788ee7a89cb586b0d8032e84c5569813d4fb0ddc2c9c7` |
| 9 | 6/7 | 3,1,2,4,1,0,0,2,7,7,8,8,5,3,4,6,6,5 | `03d89c54fa21f95db30c83c5f20a0f83d9fdf24182f5429ac346f6a93bf151b9` |
| 9 | 8/9 | 3,4,8,8,7,7,6,0,0,1,1,2,2,3,5,6,4,5 | `4afeb09d5c5f5d79f5e348c25ece4df6f93e15e3755a030e7a62ad04ad3f3bac` |
| 9 | 10/11 | 3,1,2,3,5,4,6,6,1,0,0,2,4,7,7,8,8,5 | `d206537031f106144fa5cf36423995f7957961a7bb9a37e3f880bfe0afffb7ea` |
| 10 | 2/3 | 3,0,0,1,1,3,2,5,9,9,8,8,7,4,5,7,6,2,4,6 | `0faae02be54e9fdbfc02cefc4e02e03679b27aa947900859a59bacc54f962a92` |
| 10 | 4/5 | 3,7,5,0,0,1,1,2,2,4,4,3,6,5,9,9,8,8,7,6 | `0dfc268d35d06a93767236b2b7ef25289cfe50a76241d5f982fbc05af606444d` |
| 10 | 6/7 | 3,5,1,2,2,0,0,1,4,3,8,9,9,7,7,8,5,4,6,6 | `98fb1056cf653597d7a9d92584c0b3db45f74c8eed3239e575f47adbc17ccdfd` |
| 10 | 8/9 | 3,4,7,7,5,1,1,0,0,3,2,2,6,9,9,8,8,5,4,6 | `d08ade64e3801379ee4eb8bcd3e25b88d3e55ad53eb6530fdf65ea97fa19a77f` |
| 10 | 10/11 | 3,4,2,1,4,5,7,3,1,0,0,2,6,7,8,8,9,9,5,6 | `5ae517b65bede07a2f401afb2878620f2a3e57b6df326f3d72af4bef52f52de2` |
| 11 | 2/3 | 3,0,0,1,1,3,2,6,10,10,9,9,8,5,7,8,6,4,5,2,4,7 | `2a0f480d147f798e14bf8c9f797c4a1106cb1bb8e26735a37493576247939451` |
| 11 | 4/5 | 3,6,5,0,0,1,1,2,2,4,4,3,7,5,10,10,9,9,8,8,6,7 | `fc18f94d6fafeab598b7199c3fe7d61c41e988ac4740d7ba08cea31bbebecb4a` |
| 11 | 6/7 | 3,5,1,2,2,0,0,1,4,3,7,10,10,9,9,4,5,6,6,8,8,7 | `9765ee16aaf9658e109814282cd2892cc079565dcd34637d5e6460f736433c2b` |
| 11 | 8/9 | 3,3,1,2,6,5,2,0,0,1,4,6,10,10,9,9,8,4,5,8,7,7 | `6b9d533329521e0df663043edb90e9e5247132627aec5fa93a7ed6aa08d640a7` |
| 11 | 10/11 | 3,3,1,2,7,6,5,5,2,0,0,1,4,4,8,10,10,9,6,8,9,7 | `7fc7d85b19f93db6ce9811a4e295f35b0482ffb2c99ccd3cc95bc94db874a904` |
| 12 | 2/3 | 3,0,0,1,1,3,2,6,11,11,10,10,9,9,7,7,8,5,6,4,5,2,4,8 | `c8ee665fe8a54196df7f26c718b75ba9fbb2bc7ae071a227ccb320270747f3f4` |
| 12 | 4/5 | 3,3,5,0,0,1,1,2,2,5,4,6,6,7,9,11,11,10,8,9,10,4,7,8 | `398b830f236c579d5ec19a1bc52297570acb8b29e04fd1d92cc39ce3b0a98cc3` |
| 12 | 6/7 | 3,5,1,2,2,0,0,1,4,3,8,9,10,10,11,11,7,7,9,6,6,4,5,8 | `87cba8bbbadce112dc21d739952ddc887af915db18074a80d921daf9004f0359` |
| 12 | 8/9 | 3,3,1,2,6,5,2,0,0,1,4,6,7,7,10,9,9,11,11,10,5,4,8,8 | `e07cd8a187a3cbf895bf3f0d412d5d469a4d435307fb455f91f9e3464f0a5af4` |
| 12 | 10/11 | 3,4,8,7,6,2,1,3,2,0,0,1,5,6,4,5,9,11,11,10,7,9,10,8 | `c8adec1ce76c033cb2ecb31c4ad214a951347276819ed604112d68470862c133` |
| 13 | 2/3 | 3,0,0,1,1,3,2,6,12,12,11,11,10,10,9,8,8,7,7,5,6,4,5,2,4,9 | `d67b91766443f19d58c4e09f49c4bb5bde5f4e325bb185a4e8c478991a4d900b` |
| 13 | 4/5 | 3,5,5,0,0,1,1,2,2,4,7,6,6,3,4,10,12,12,11,8,10,11,9,7,8,9 | `25eceacafb21152c014d2966e0c187ece1f41585f768e665e3234a603cba0e99` |
| 13 | 6/7 | 3,5,1,2,2,0,0,1,4,3,8,11,12,12,10,10,11,7,9,8,7,6,6,4,5,9 | `e1de5f0fd3cba57a687fa797ddcdcfe300b9602e7ba2acb406e690d642529fb0` |
| 13 | 8/9 | 3,5,8,10,9,6,4,0,0,1,1,2,5,7,10,11,11,12,12,8,6,3,2,4,7,9 | `c112c349aa1ccc82bb2825a637a1b2e157cf02ea3584c8e298f4f2635a2d42c5` |
| 13 | 10/11 | 3,5,8,8,10,10,9,6,4,0,0,1,1,2,5,7,7,4,2,3,6,11,11,12,12,9 | `665ca66643a3f1ecc4ca35416ff4bbd151c9852271ba35598cbb84ca055f0f44` |


## Appendix C. Complete compatible 48-core bank

Tags alternate H,L beginning H. At one-based depths a−1,a,a+1,a+2 the entries are H4,L0,H0,L1. Every row hash follows the canonical numeric-array convention above.

| p0 | a | Exact ordered core | SHA-256 |
|---:|---:|---|---|
| 16 | 12 | 3,3,2,7,7,5,8,9,6,4,4,0,0,1,1,2,5,6,10,8,12,13,14,14,15,15,11,11,13,10,9,12 | `208db5049800c79cdc8a482227d6f1eb5475057cf651d58b22e5e6849c62e328` |
| 16 | 14 | 3,3,2,7,10,13,15,15,14,10,8,4,4,0,0,1,1,2,5,5,6,8,11,11,9,6,7,9,12,14,13,12 | `7d960ac77021264a74840cf3e8f220d10c07643326a6a0ba2f69f874adf85f9c` |
| 16 | 16 | 3,3,2,7,10,15,15,14,14,13,13,9,7,4,4,0,0,1,1,2,5,5,8,10,11,8,6,6,9,11,12,12 | `58abc005a9260f8d2f2a506430ed242bffab4faeaa1644d969b5e23ca53c3a6d` |
| 16 | 18 | 3,4,2,3,9,9,7,8,11,11,14,13,8,6,5,5,4,0,0,1,1,2,6,7,10,10,13,15,15,14,12,12 | `57240e7485ae2268a075f4e3a1d4d89ba542b6ff795822625c7379b61372ad5b` |
| 16 | 20 | 3,3,2,6,9,9,12,13,14,14,15,15,11,11,13,10,10,7,4,0,0,1,1,2,5,4,6,8,8,5,7,12 | `818e30e51aa6318290c836404ce80dad095dda3d25537037c014006fedb9a5b8` |
| 16 | 22 | 3,3,2,6,6,4,7,7,8,9,9,10,14,13,13,15,15,14,11,5,4,0,0,1,1,2,5,8,12,11,10,12 | `db6fdc350d21627b23f898af0eb29acfcc40d19dac137697d5961b1426a9bac2` |
| 16 | 24 | 3,5,8,10,13,15,15,14,12,9,7,4,2,3,6,8,11,13,14,11,9,6,4,0,0,1,1,2,5,7,10,12 | `c185f8343e0b5a466f363b37ff3d7bafd8df4ec9132a00b057ad97f823d640ec` |
| 16 | 26 | 3,4,2,3,5,7,8,5,6,8,9,9,12,13,14,14,15,15,11,11,13,10,10,6,4,0,0,1,1,2,7,12 | `fffd765b8bcb8c039ca94754962361e3d14255c24ea792ca6423503dcf12cd5c` |
| 17 | 12 | 3,3,2,6,9,11,13,10,8,5,4,0,0,1,1,2,5,7,10,12,15,16,16,14,14,15,11,8,6,4,7,9,12,13 | `15d5e62820031adc73369c40cc94c28e473d21db974c33eb70c5087c8696b5c4` |
| 17 | 14 | 3,3,2,6,9,11,14,15,13,10,8,5,4,0,0,1,1,2,5,7,10,12,15,16,16,14,12,9,7,4,6,8,11,13 | `5dba43c0309559c0347a90a83c242e458423d5f56a3be45299be1e320ba0da51` |
| 17 | 16 | 3,6,8,5,7,8,11,15,16,16,14,9,9,7,4,0,0,1,1,2,5,3,2,4,6,11,10,10,12,12,13,14,15,13 | `e147620d03d68604e01ef31e7557b744289349558e0748788b49c95436b13a68` |
| 17 | 18 | 3,4,2,3,5,8,11,9,9,14,14,11,10,7,8,6,4,0,0,1,1,2,7,5,6,10,12,12,15,15,16,16,13,13 | `3e0069e5cbceb3b80c003907acaec19496a76a41d2e42407dd7e885cbd91b227` |
| 17 | 20 | 3,4,2,3,7,9,10,15,16,16,14,12,12,11,11,10,8,5,4,0,0,1,1,2,6,8,9,6,5,7,13,14,15,13 | `f082fcf4ba9225e4d51de41fd2c25421872642ad6d49f7b30c2a49fb8a656e88` |
| 17 | 22 | 3,3,2,6,8,10,11,16,16,15,15,14,14,12,10,9,6,4,7,5,4,0,0,1,1,2,5,8,9,7,13,11,12,13 | `c94118a9c38321ba4c355496915619d1d403f12d01914ae6d97f3fc06ab50c46` |
| 17 | 24 | 3,4,2,3,7,9,12,14,16,16,15,12,10,7,8,10,13,15,14,11,9,5,4,0,0,1,1,2,6,6,5,8,11,13 | `2a912cce0aeabce796f477e835d06b3ed4e6bbd3afed6bf850f1a48493896760` |
| 17 | 26 | 3,6,9,11,14,16,16,15,13,10,8,5,5,7,10,12,15,14,12,9,7,4,2,3,4,0,0,1,1,2,6,8,11,13 | `38176fab4267ef551c38008e26395ea89066ef558053bbdfce976e4af06c093e` |
| 18 | 12 | 3,3,2,6,9,11,13,10,8,5,4,0,0,1,1,2,5,7,10,12,14,17,17,16,16,13,15,15,12,9,7,4,6,8,11,14 | `ecbbcf1c35a1a274e2830102cccf2319e128efa44a1b576f3eb3339048571e15` |
| 18 | 14 | 3,3,2,6,9,10,11,11,12,12,8,5,4,0,0,1,1,2,5,7,10,8,6,4,7,9,16,15,14,16,17,17,15,13,13,14 | `7ce93d2e44e38407f20e1b9189d81d369c5c2b440c09fdd9165515c3a7233522` |
| 18 | 16 | 3,3,2,7,10,12,14,15,15,13,12,9,7,4,4,0,0,1,1,2,5,5,8,10,13,11,9,6,6,8,11,16,16,17,17,14 | `b105096bec9c47fa6694b51157289f53d0c737f8076fd14abffd4f5c2803c93b` |
| 18 | 18 | 3,6,9,11,13,10,8,5,7,9,12,13,15,12,10,7,4,0,0,1,1,2,5,3,2,4,6,8,11,15,14,16,16,17,17,14 | `64095b598c89aa89ae8b375a0ba659f523431051793d800a460b3c97f39b6cef` |
| 18 | 20 | 3,6,8,10,13,12,10,7,9,11,15,15,16,16,17,17,12,9,4,0,0,1,1,2,5,3,2,4,6,5,7,8,11,13,14,14 | `a29a7c5f90d9bf51e09743f9e693d5df3302a863022dcc6dcc0858b72bed4d23` |
| 18 | 22 | 3,5,9,10,8,9,15,16,16,17,17,13,14,15,13,12,11,11,10,6,4,0,0,1,1,2,5,7,6,3,2,4,7,8,12,14 | `04912068c16c5e8f177d292de2e69eed70869781c840c0f274261a922128f7d4` |
| 18 | 24 | 3,4,2,3,7,9,12,12,10,10,13,15,16,13,14,16,17,17,15,11,8,5,4,0,0,1,1,2,6,8,9,6,5,7,11,14 | `f7aef0d786f7271f7b4992458c32549bf051fac4362a440674933eb1dcbe476f` |
| 18 | 26 | 3,4,2,3,7,9,12,16,15,15,17,17,16,13,14,12,10,7,8,10,13,11,9,5,4,0,0,1,1,2,6,6,5,8,11,14 | `d53d39bb9476abe5d6d7762f0e9adf98cbc609dde356105bf505de3e12edd345` |
| 19 | 12 | 3,3,2,6,9,11,13,10,8,5,4,0,0,1,1,2,5,7,10,12,14,13,12,9,7,4,6,8,11,17,18,18,16,14,15,16,17,15 | `e12ac50e47928d4d0c9f867803a2c88afa5016235fde8dcf02bbd994123a2176` |
| 19 | 14 | 3,5,8,8,6,3,2,4,7,10,9,6,4,0,0,1,1,2,5,7,11,9,15,17,18,18,16,13,12,11,10,12,14,16,17,14,13,15 | `f5de4eb0695f2a92859fc1eabd1840e32e6188c813893d8a5bbbbea04c11b464` |
| 19 | 16 | 3,7,11,13,18,18,17,17,16,16,14,9,8,5,4,0,0,1,1,2,5,3,2,4,7,8,6,6,10,11,9,10,12,14,15,12,13,15 | `b2c95a45eef71ec42aa47486cd147fe1be5d9b7fa7a8cddf2286fd060d7fd58c` |
| 19 | 18 | 3,5,8,10,11,8,6,3,2,4,7,9,14,11,9,6,4,0,0,1,1,2,5,7,10,12,12,14,13,18,18,17,17,16,16,13,15,15 | `697463fe734abcf9a3f291c702bb65654f7de5b3a92b69219c61110ed2af3f69` |
| 19 | 20 | 3,4,2,3,5,6,9,11,14,14,16,18,18,17,12,9,7,5,4,0,0,1,1,2,8,10,13,13,11,8,6,7,10,12,15,16,17,15 | `9a52295791ccd14c4d2af511aa1c4570e93915923e4b5831211121547f76b9f0` |
| 19 | 22 | 3,3,2,6,9,11,13,13,16,14,14,18,18,17,17,16,15,10,8,5,4,0,0,1,1,2,5,7,10,12,11,8,6,4,7,9,12,15 | `224cfff1512df1cb72398b1c7a2e93f3d19d31cb8f9e5743bbdbe31c2bc107cd` |
| 19 | 24 | 3,3,2,6,7,4,6,8,8,9,14,16,18,18,17,14,12,10,9,11,10,5,4,0,0,1,1,2,5,7,11,13,16,17,15,12,13,15 | `8055192f91b5b80b3ae651415f13794ce3afb848f32d590c0cc0646c7cdf0ce2` |
| 19 | 26 | 3,3,2,5,8,11,13,13,17,18,18,16,16,17,14,14,15,10,7,4,5,7,9,6,4,0,0,1,1,2,6,8,10,12,11,9,12,15 | `7d6d706e19ae90c8927457775550616bb905b732fc8c07889e9ce9a14ffc0c79` |
| 20 | 12 | 3,3,2,6,9,11,13,10,8,5,4,0,0,1,1,2,5,7,10,12,14,17,18,15,12,9,7,4,6,8,11,14,15,13,17,19,19,18,16,16 | `82b01a2190cc3411d8d75432e985220f8102bd8f48c1aff177a90af7bdd92466` |
| 20 | 14 | 3,3,2,6,9,10,7,4,6,8,8,5,4,0,0,1,1,2,5,7,11,9,13,12,14,13,19,19,18,18,17,17,16,15,15,14,10,11,12,16 | `87848e4a15d48db8ba38802322899e4f47f2d1ee0f1109add427c5ef55606226` |
| 20 | 16 | 3,4,2,3,8,11,14,12,10,7,9,9,5,5,4,0,0,1,1,2,6,6,7,8,12,15,17,19,19,18,13,10,11,13,15,14,16,17,18,16 | `08fee7aeee1c12a89e15132d41239d2204671f88c3487a7433d09a078162c10c` |
| 20 | 18 | 3,3,2,6,9,11,14,15,18,19,19,17,13,10,8,5,4,0,0,1,1,2,5,7,10,12,15,13,11,8,6,4,7,9,12,14,17,18,16,16 | `5382aa2f3c036e4b884d0eecc2cdc59a5fd4f817cf2f4a9026d0a04425b75e05` |
| 20 | 20 | 3,3,2,6,9,11,14,12,10,8,11,13,15,17,12,9,8,5,4,0,0,1,1,2,5,7,7,4,6,10,13,14,16,15,19,19,18,18,17,16 | `df96e6cfc5cc55594ff529fe845d335a5d5121c799bace39a3bc81e28a566b6e` |
| 20 | 22 | 3,3,2,6,9,11,14,13,15,14,19,19,18,18,17,17,13,10,8,5,4,0,0,1,1,2,5,7,10,12,12,9,7,4,6,8,11,15,16,16 | `ad35372d308123404182566191f390cfc31d4a5622486b982fe7c52a9b6568c7` |
| 20 | 24 | 3,3,2,6,10,12,15,13,11,8,9,11,14,15,18,19,19,17,13,10,8,5,4,0,0,1,1,2,5,7,7,4,6,9,12,14,17,18,16,16 | `289e418b29bdd7a09129d7de134f7bcf1de88b78466b591e83d65cc4b621c993` |
| 20 | 26 | 3,3,2,7,10,12,15,13,11,8,6,6,9,11,14,15,17,17,16,14,12,9,7,4,4,0,0,1,1,2,5,5,8,10,13,18,18,19,19,16 | `b15494a2a1e32f6d1a3b7d4777d9a6d90b14d21d85e6787726aa10e6ee881d5c` |
| 21 | 12 | 3,7,10,12,15,13,11,8,6,5,4,0,0,1,1,2,5,3,2,4,8,10,13,16,20,20,19,19,18,15,17,18,16,14,12,9,7,6,9,11,14,17 | `184ca4d47a7012f840aeb7ce051541fb5b9fbda28e41e920f76a67f441a6aa77` |
| 21 | 14 | 3,3,2,6,9,10,7,4,6,8,8,5,4,0,0,1,1,2,5,7,11,9,15,15,16,20,20,19,19,18,17,16,18,14,14,13,13,12,10,11,12,17 | `751f79f394251b042940dba82d898ca115ea15b2ee7d289cc83ceeff6fe45f7d` |
| 21 | 16 | 3,3,2,6,9,11,14,15,18,18,13,10,8,5,4,0,0,1,1,2,5,7,10,12,15,13,11,8,6,4,7,9,12,14,16,16,19,19,20,20,17,17 | `9107827d333d9ed82b234ab7549455ce353431f2b5c97849c0b7f0d71168c6fc` |
| 21 | 18 | 3,3,2,6,9,11,10,9,13,10,7,4,6,8,8,5,4,0,0,1,1,2,5,7,11,14,17,16,12,12,14,13,16,19,20,20,18,18,19,15,15,17 | `d947fda02f8daac42581658ff36eb7dc2fcf44a6a7d19160e795584ee13f71d1` |
| 21 | 20 | 3,4,2,3,5,6,9,11,11,8,6,7,10,14,12,9,7,5,4,0,0,1,1,2,8,10,13,12,16,18,18,15,14,13,17,20,20,19,19,16,15,17 | `e09d9a8007bbb38ff2b218b8b13f83f9ced9652ee1bf9c492dd365f12206e9c3` |
| 21 | 22 | 3,3,2,6,9,8,10,9,11,11,14,18,19,19,20,20,16,13,8,5,4,0,0,1,1,2,5,7,7,4,6,10,13,15,15,12,12,14,17,16,18,17 | `30c1fe7fa04f4320935228005290f496a8ba69d8cc621d0a1830a2b6c988a7f1` |
| 21 | 24 | 3,6,8,5,7,8,9,9,10,12,15,20,20,19,19,18,18,16,17,15,13,7,4,0,0,1,1,2,5,3,2,4,6,10,11,13,16,14,12,11,14,17 | `605355532b4353cf9d25e848ff70f52114634b86d8aeab328c45372274c60ca0` |
| 21 | 26 | 3,3,2,6,9,11,13,13,14,14,20,20,19,19,18,18,17,16,16,15,15,10,8,5,4,0,0,1,1,2,5,7,10,12,11,8,6,4,7,9,12,17 | `fbbf28b43c82e42d0e6b23cb90c44577a410af7ae0d16a4c702e79d11000fc42` |

## Appendix D. Exact universal insertion gadgets

P starts H; B and D start L. Each displayed block has even length; δ=len(P)+len(B). Constants are bound by old-data.json and gadget30.json in the source inventory.

| q | δ | P | B | D |
|---:|---:|---|---|---|
| 9 | 4 | 3,6 | 9,4 | 1,1,2,5,3,2,4,6,5,7,7,8,8,9 |
| 9 | 6 | 3,5,6,6 | 9,4 | 1,1,2,5,4,2,3,7,7,8,8,9 |
| 9 | 8 | 3,6 | 9,7,5,8,7,4 | 1,1,2,5,3,2,4,6,8,9 |
| 9 | 10 | 3,7 | 9,9,6,5,4,2,3,4 | 1,1,2,6,8,8,5,7 |
| 9 | 12 | 3,6 | 9,8,5,6,8,7,3,2,4,4 | 1,1,2,5,7,9 |
| 9 | 14 | 3,7 | 9,9,8,8,6,7,5,6,3,2,4,4 | 1,1,2,5 |
| 18 | 30 | 3,6,11,16 | 18,18,17,17,15,16,14,15,13,13,12,12,10,9,11,10,8,8,5,5,7,7,4,2,3,4 | 1,1,2,6,9,14 |

## Appendix E. Six tracked-pair source cores and their reflected certificates

Source arrays are exact rows of Appendix C and data.json SHA-256 3eec37728f84b9462617615163880a0ba8a04e451cf9edf4831ec55000a75685. Reflected arrays are T_p(C), with tags reset H,L from the first entry; their hashes use the same compact-JSON convention. Numeric zeros on opposite tags remain distinct.

| p | Original anchor | Original-array SHA-256 | Reflected ordered array | Reflected zero depths/order | Reflected-array SHA-256 |
|---:|---:|---|---|---|---|
| 16 | 16 | `58abc005a9260f8d2f2a506430ed242bffab4faeaa1644d969b5e23ca53c3a6d` | 3,3,4,6,9,9,7,4,5,7,10,10,13,14,14,15,15,11,11,8,6,2,2,1,1,0,0,5,8,13,12,12 | 26/27 L0,H0 | `a8e38aec5b0c016ef4e4fd855a7c1d05066ca5d0b8be575457e819d827c97226` |
| 17 | 22 | `c94118a9c38321ba4c355496915619d1d403f12d01914ae6d97f3fc06ab50c46` | 3,4,5,3,9,7,8,11,14,15,15,16,16,12,11,9,12,10,7,6,4,2,2,1,1,0,0,5,6,8,10,14,13,13 | 26/27 L0,H0 | `a94d1a97b42dee177a448ccd06521dce7652b1f878038604cdfea92ba91cfe1d` |
| 18 | 22 | `04912068c16c5e8f177d292de2e69eed70869781c840c0f274261a922128f7d4` | 3,5,9,10,13,15,14,11,10,12,15,16,16,17,17,13,11,7,6,6,5,4,2,3,4,0,0,1,1,2,8,9,7,8,12,14 | 26/27 L0,H0 | `d074ba47c88046dcc217cf69d0dc51384f287a4a23aa9d88c25774c78acd666e` |
| 19 | 20 | `9a52295791ccd14c4d2af511aa1c4570e93915923e4b5831211121547f76b9f0` | 3,1,2,3,6,8,11,12,10,7,5,5,8,10,16,17,17,18,18,14,13,11,9,6,1,0,0,2,4,4,7,9,12,13,15,16,14,15 | 26/27 L0,H0 | `0637913effc4282cd974207045f0d012caa213cd3ba26d1bf30e78c250308837` |
| 20 | 24 | `289e418b29bdd7a09129d7de134f7bcf1de88b78466b591e83d65cc4b621c993` | 3,3,1,2,5,7,10,13,15,12,12,14,17,18,18,19,19,15,14,11,9,6,2,0,0,1,4,5,8,10,11,8,6,4,7,9,13,17,16,16 | 24/25 L0,H0 | `42c357e0edad8f6042f8b5ec346a8c66886254acf7cebbd3bb57022f324cb97f` |
| 21 | 22 | `30c1fe7fa04f4320935228005290f496a8ba69d8cc621d0a1830a2b6c988a7f1` | 3,2,4,3,6,8,8,5,5,7,10,14,16,13,13,15,18,19,19,20,20,16,15,12,7,4,0,0,1,1,2,6,9,9,11,10,12,11,14,18,17,17 | 27/28 H0,L0 | `65d446bc56accf16374dada38df0907a9bc80aea86cb2da2d26b5fe0f30e1f2e` |

## Appendix F. Exact q11 global-prefix base and bridge recipes

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

The q11 P/B/D literal is given in Section 7.1. The ordered replacement-chain sums are (11,22); (26,21,15,10,9,6,5,7,4); and (1,2,3,8,12,13,14,16,19,18,17,20,23). Their disjoint union is [1,23]∪{26}. These tables are positive finite certificates supporting the universal translated bridges; they assert no optimum over unrestricted labelings.
