# Separate internal audit of the reverse-complement depth construction

Private mathematical record, 9 October 2026. **GO for the exact theorem in
sections1--5 of the frozen author report bound below.** The mathematical
reconstruction and separate executable checks pass. No external
review, scholarly peer review, Lean proof, optimality or historical priority
claim is made. Jordi Gartner owns and publishes this work through Beedbyte.
AI assistance supported the mathematical reconstruction and separate code and
checks documented here. No public release or shared checkpoint is changed.

## Exact statement reconstructed

For all integers k>=19, define D6(k)=11 for 19<=k<=34, D6(k)=27 for
35<=k<=52, and, for k>=53, put

    U=floor((k-35)/18),   D6(k)=25+16U.

For every n>=2,m>=0, every specified long arm of S(k^n,1^m), and each
integer depth 2<=d<=D6(k), there exists a graceful labeling assigning zero
to the specified depth-d vertex. Requests may use different labelings.
The claim is a sufficient prefix, not full zero-rotatability. It depends on
the precisely bound accepted D5 core prefix and the generic odd/even shell
lemmas, with the new reconstruction supplying the extension to D6.

Equivalently K6(d)=19 for 2<=d<=11, K6(d)=35 for 12<=d<=27, and

    K6(d)=35+18 ceil((d-25)/16),  d>=28.

Every integer k>=K6(d) satisfies the prescribed-zero conclusion. This is a
sufficient threshold of this construction, not a least possible threshold.

## Independence and input scope

AGENTS.md, EDITORIAL_POLICY.md and the current RESTART were read. The frozen
compatible-seed author proof, its separate audit, the q18 gadget audit, the
even-shell proof/audit and the final combined D5 acceptance were read as
mathematical premises. The six literal selected cores and q9 gadgets are from
the accepted compatible-seed package; no new search certificate is needed.
The independent audit imports only Python's standard library. It neither
imports nor executes author source or a solver. Graph insertion is reconstructed
by edge deletion/subdivision and path traversal, rather than the author's
array-splice operation. Actual spider adjacency is built separately from labels
and checked by BFS. Exact source/report bindings are in source-inputs.json.

## Reverse-complement lemma, including tag orientation

For a balanced size-p core C, with indices 0 through 2p-1, define

    T(C)[i]=p-1-C[2p-1-i].

Target index i receives H if i is even and L otherwise. The source index has
the opposite parity because 2p-1 is odd. Thus T's H offsets are complements
of C's L offsets, and T's L offsets are complements of C's H offsets. Both
are permutations of 0,...,p-1. Its consecutive sum at i is 2p-2 minus C's
consecutive sum at 2p-2-i. This bijects the sum interval 0,...,2p-2. Its first
entry is p-1-(p-4)=3, and its last is p-1-3=p-4. Applying T twice returns C.

Sum 2p-2 forces C's unique maximum H(p-1),L(p-1) vertices to be adjacent,
in either order. If their first index is t, their image consists of zeros
at indices 2p-2-t,2p-1-t, hence depths b,b+1 where b=2p-1-t. The image
ordering may be L0,H0 or H0,L0. The generic shell requires neither ordering
nor the original H4,L0,H0,L1 window, so both are valid. T need not preserve
that window: all compatible insertions are performed BEFORE T.

## Tracking the maximum pair through insertion

Use the literal q9 gadgets indexed by old-zero displacement4 and6. Their P
lengths are respectively2 and4; each B length is2, and D lengths are14 and12.
Each P begins H3 and ends L, each B/D begins L and ends H. All values are
positive. Every new tagged side separately permutes1,...,9. B ends H4 and D
starts L1. The three replacement chains have sums1,...,19 and22 exactly once.

To see the universal algebra, shift every old positive offset by9 and retain
the two zeros. Cut H13-L0 and H0-L10, prepend P to the old first H12, and
insert B and D along the two cut edges. Every surviving positive-positive
sum increases by18. The old sums1 and4 were cut, sum0 survives, and the
retained sums are {0} union ([20,2p+16] minus {22}). The replacement chains
fill exactly the complement. The resulting size is p+9, both side permutations
are complete, the endpoints are H3,L(p+5), and the compatible zero window
persists. Positivity matters: every old maximum remains positive, moves to
p+8, and exceeds every new gadget offset because p>=16.

The selected initial maximum pair is entirely BEFORE the old zero pair.
Its internal edge is not one of the cuts, and inserting B/D at the later
zero edges cannot change its index. Only P precedes it. Thus its first index
advances by2 or4, while the core length advances by18. It remains before
the zero pair, so the argument iterates without an orientation exception.
After T, the first zero depth consequently advances by16 or14, respectively.

For j moves, of which s use P length2, every s=0,...,j is allowed and gives
the consecutive depths

    b+14j+2s, b+14j+2s+1.

Their union is the full integer interval [b+14j,b+16j+1], regardless of
whether b is odd or even. This is where the opposite p21 orientation matters.

## Six residues, depth interval and the existing prefix

The selected rows (p0, old-zero anchor) are (16,16), (17,22), (18,22),
(19,20), (20,24), (21,22). Direct checking gives reflected pair starts

    b = 26,26,26,26,24,27.

The first five reflected pairs have order L0,H0; the last has order H0,L0.
All original maximum pairs precede the old zero pair. The six per-seed full
depth intervals have common intersection

    I_j=[27+14j,25+16j],   j>=1.

This is already an interval of DEPTHS, including the second vertex of each
pair. It is not an interval of pair starts to which another +1 may be added.
For j=1, I_1={41}. The p20 residue only reaches depth41 by this choice,
so this argument does not establish a universal additional depth42 at U=1.

For a target p and any j with p>=16+9j, divide p-16-9j=6r+delta with
0<=delta<=5. Select p0=16+delta, perform j insertions, apply T at size p0+9j,
and only then append r translated C6 cores. The appended core is

    C6=[3,3,2,1,1,0,0,4,4,5,5,2].

At size x, append x+C6. It supplies each side x,...,x+5, internal sums
2x,...,2x+10 and bridge sum (x-4)+(x+3)=2x-1. Hence the complete next sum
interval and endpoints persist. Since x>0, its entries are positive, so
the reflected zeros and their positions are unchanged. This proves every
target-size residue without assuming that T and append commute.

Set U=floor((p-16)/9). When U>=1, the accepted D5 prefix ends at
F(U)=27+14U+2floor(U/2). This is at least I_U's lower endpoint27+14U.
Thus the new interval overlaps the old prefix. Its upper endpoint exceeds
F(U) by U+(U mod2)-2: zero at U1,2 and positive at U>=3. Consequently
the union covers every depth2,...,25+16U. The first strict gain is U3,
k89/90: D5=71 becomes D6=73. For U0 and p8..15 the inherited prefix is used.

## Actual spider transfer and all k

The generic odd and even shells apply because T and append preserve exactly
the endpoint, side-permutation and consecutive-sum contract. For odd k=2p+3,
put M=4p+6,A=2p+2; map Hh to M-h and Ll to l on the selected arm, then use
tail (3p+3,p+1,3p+4). The partner is the p pairs
(2p+3+i,2p+1-i), followed by (3p+6,p,3p+5). Center A and these arms partition
0,...,M and differences1,...,M, with every edge crossing A.

For even k=2p+4, put M=4p+8,A=2p+4. The selected tail is
(3p+5,p+2,3p+7,p+3), while the partner pairs are
(2p+5+i,2p+3-i), followed by (3p+6,p,3p+8,p+1). The selected core weights
are2p+10,...,M; its center edge has weight2p+1; the eight tail edges supply
2p+2,...,2p+9, and the partner prefix gives1,...,2p. Vertex bands and crossing
likewise agree with the accepted generic even shell.

For h=n-2 and Q=hk+m, the other arms use residual labels
(h-i)k-(t-1)/2 at odd depth t and ik+t/2 at even depth t, for i=0,...,h-1.
These, with leaves hk+1,...,hk+m and center0, partition0,...,Q and differences
1,...,Q. Add A to residual noncenter labels; add Q to the shell labels above
A. The full labels partition0,...,N where N=nk+m, and differences partition
1,...,Q and Q+1,...,N. This includes h0,Q0. Every selected L0 is zero;
every selected H0 is N. Complement the ENTIRE graph by N-x when targeting
H0. In particular the p21 reflected pair gives zero at its odd first depth
after complement and its even second depth without complement. No restriction
requiring an even first pair depth exists.

Any specified arm can be selected, with any distinct partner because n>=2.
The core depths are unchanged because tails are appended and the center is
not included in core indexing. For odd k, U=floor((k-35)/18). For even k,
U=floor((k-36)/18)=floor((k-35)/18), because adding1 to an even numerator
cannot cross a multiple of18. The inherited bounds cover19..52; these two
shells supply the new formula from53 onward without parity gaps.

## Legal depths, limiting fraction and thresholds

Write k=35+18U+r,0<=r<=17. For U>=1,

    8k-9D6(k)=55+8r,  hence 55<=8k-9D6(k)<=191.

For U0 it is37+8r, and for19<=k<=34 it is8k-99. Thus globally
0<=8k-9D6(k)<=191, proving D6(k)/k tends to8/9 through all integer lengths.
The constant191 is attained, for example at k70 with D6=41.
Also D6(k)=25+16U<35+18U<=k when U>=1; the earlier constant pieces have
the same strict legal-depth property. D6 is nondecreasing, and inversion of
its constant pieces and slope16 steps gives K6 as stated. This establishes
an improved limiting sufficient prefix, not an optimality theorem.

## Separate executable evidence

Normal Python and python -O give identical results. The audit uses explicit
exceptions rather than assertions. Its finite scope is:

- All48 compatible seed literals, all30 small seed literals and all7 original
  q9/q18 gadget identities are checked. Only two q9 gadgets generate the new
  intervals; the q18 identity is a consistency check on the inherited premise.
- All378 binary move words through five steps across the six selected seeds
  are reconstructed by graph edge operations, checking maximum positions and
  reflected zero depths. In all,6,762 graph insertions and25,239 core checks pass.
- 755 final new cores cover every choice at p25..106 and selected lower-j
  cases up to p160, including positive C6 padding after reflection.
- 5,252 actual spiders cover both shell parities at p in
  {25,26,30,33,34,35,42,43,44,51,52,53,60,61,62,70,79,88,97,106}; parameters
  (n,m) in {(2,0),(2,3),(3,0),(4,2),(7,1)}; arms0,floor(n/2),n-1 (deduplicated);
  and both zero/extreme depths for every generated move count. Complete label
  and edge bijections and actual center-to-target BFS distances are checked.
- 199,982 lengths k19..200000 check floor identities, old-prefix overlap,
  nonregression, monotonicity, legal depths and the stated asymptotic bound.
  A further9,999 requested depths d2..10000 verify the threshold and the
  preceding-length boundary of the piecewise inverse K6.
- Thirteen negative controls reject partial target complement, duplicate
  labels and reversed arm order in both shell parities, a bare core reversal,
  off-by-one offset complement, damaged core, n1, absent selected arm, wrong
  target depth, and a nonpositive gadget entry.

These finite results diagnose implementation and boundary errors. The universal
proof is the tag/sum involution, preserved maximum-pair position, universal
gadget identity, interval union, six-residue padding and actual-spider transfer
above, composed with the accepted D5 premise. They are not inferred from the
finite test range. An initial auditor draft guessed the too-small global
deficit bound173; its arithmetic check rejected that guess. The correct191
bound is derived above and passes both final executions.

The frozen author's saved literals were also checked after author freeze,
without reading, importing or executing its Python source. check_saved.py
uses our own graph constructor to reconstruct all748 saved cores exactly,
verifies their complete recipes and common-depth coverage at p25..106, and
directly checks all1,760 saved actual spiders by label/edge permutations and
BFS. It rejects five additional corruptions: duplicate label, missing center,
wrong depth, partial target complement, and an absent arm. Normal and optimized
executions agree. The saved data contains the exact six inherited cores and
two inherited gadgets claimed; all10 author manifest payload hashes match.

Replay in this immutable workspace with standard Python:

    python -B audit.py
    python -B -O audit.py
    python -B check_saved.py
    python -B -O check_saved.py

## Final binding and verdict

Author directory: graceful-beyond-five-sixths-block-principle-2026-10-09-a.
The final frozen author report was read and compared with the independently
derived proof. Its theorem, orientation treatment, order of operations,
interval endpoints and all-parity transfer agree exactly. The following
SHA-256 bindings are enforced by check_saved.py:

| Author artifact | SHA-256 |
|---|---|
| report.md | `680c39948d7562214de814052eda2bf0bf1b59fa642a757e33c7a4cd82a4014e` |
| manifest.json | `493d49feeb015cf8b776cbf2c9e9443f98431fed6018f0122d2e47831c15239d` |
| data.json | `3eec37728f84b9462617615163880a0ba8a04e451cf9edf4831ec55000a75685` |
| certificates.json | `2d717e2243f9d390fc18df7ef1ae5fdea00e0a2076859232f3ccb5507ee4d270` |

source-inputs.json additionally binds every author source/result file and
the predecessor proof/audit reports and manifests. All inherited manifest
payloads are checked before the final audit runs, and all bound input bytes
are checked again afterward. Our own manifest binds report, source and
four normal/optimized result files. Earlier historical reports and source
bytes have not been edited.

**GO** covers the new reverse-complement argument, the two q9 identities,
the six literal selected seeds, every target-size residue, the common DEPTH
interval (with no extra +1), the p21 H0,L0 orientation, joining D5, both
actual-spider shells, the exact all-k D6 theorem and the8/9 limit. The K6
inverse is an additional elementary corollary proved in this audit. No
counterexample or unresolved mathematical premise was found beyond the
explicitly inherited and authenticated D5 and generic shell theorems.

The author's literature and novelty discussion is outside this mathematical
acceptance; no primary-source search was performed here. Historical priority,
optimality, full near-tip coverage, external review and Lean formalization
of the new theorem remain unestablished. This private GO is not a publication
decision. No site, CMS, profile, shared RESTART or cycle file was changed.
