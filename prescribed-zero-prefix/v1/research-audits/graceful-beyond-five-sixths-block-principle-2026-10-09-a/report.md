# Reverse-complement tracking raises the prescribed-zero prefix to 8/9

Private author mathematical record, 9 October 2026. **Positive universal
theorem candidate, pending separate internal mathematical audit.** This package
changes no earlier evidence, RESTART, cycle record, formal package, website or
publication. No external review, Lean proof, historical novelty or full
zero-rotatability is claimed. Jordi Gartner owns and publishes the work through
Beedbyte. AI assistance here supported the symmetry argument, exact arithmetic,
construction and separate executable certificate checks.

## 1. Exact theorem and improvement

For every integer k>=19 define

    D_rc(k) = 11                                      for 19<=k<=34,
              27                                      for 35<=k<=52,
              25+16U, U=floor((k-35)/18)               for k>=53.

For all n>=2, m>=0, every selected long arm a of S(k^n,1^m), and every
integer depth d with 2<=d<=D_rc(k), there is a graceful labeling assigning
zero to the actual vertex (a,d). The labeling may depend on the requested
vertex. Both parities of k are included; no m>=1 assumption is imposed.

The quantitative bound is

    0 <= 8k-9D_rc(k) <= 191,

so D_rc(k)/k tends to 8/9 through ALL integers. This exceeds 5/6 by 1/18.
Every requested depth is legal since 9D_rc(k)<=8k<9k.

The accepted compatible-seed bound is

    D5(k)=27+14U+2 floor(U/2)  (k>=35),

with the same U, and D5=11 at 19..34 after the accepted even-shell transfer.
At U=0,1,2 the new bound agrees. At U>=3 its gain is

    2U-2 floor(U/2)-2 = U+(U mod 2)-2 > 0.

The first strict improvement is k=89,90: D5=71 becomes D_rc=73.
Examples at the next boundaries are k=107,108: 87 becomes 89; and
k=125,126: 101 becomes 105. This does not supersede stronger isolated
complete-length results at k15,k21,k27, or imply the missing near-tip depths.

## 2. Algebraic gate and a different principle

A balanced core of size p is an alternating H,L list C of length 2p, each
tag side a permutation of 0,...,p-1, with consecutive numeric sums exactly
0,...,2p-2. The shell contract fixes its endpoints H3,L(p-4).

Before selecting an extension, the degree-sum identity forces the endpoint
offset sum to p-1: the total edge sum is both (p-1)(2p-1) and
2p(p-1)-(first+last). Moreover, sum 0 forces H0 adjacent to L0, and
sum 2p-2 forces H(p-1) adjacent to L(p-1). Thus EVERY balanced core
contains two distinguished adjacent extreme pairs, not merely the zero pair
tracked by the old insertion proof.

Define the reverse-complement map

    T_p(C)[i] = p-1-C[2p-1-i],  0<=i<2p,

and assign its alternating tags anew, H at even i and L at odd i. Reversal
interchanges source tag sides; complementation permutes each 0,...,p-1.
Consecutive sums map by s -> 2p-2-s. Endpoints become
p-1-(p-4)=3 and p-1-3=p-4. Consequently T_p preserves the full balanced
shell contract and is an involution.

If the old maximum pair starts at ZERO-based index t, its transformed zero
pair occupies ONE-based depths

    b=2p-1-t, b+1=2p-t.

The order may be L0,H0 OR H0,L0. Each order supplies both depths in the
actual spider: low zero gives zero directly, and high zero gives the graph
maximum, which becomes zero after global complementation.

This symmetry is the new organizing principle in this package. It reuses
accepted q9 certificates and follows their OTHER extreme pair. It neither
reruns q24 search nor introduces another P/B/D enumeration. In particular,
8/9 is a consequence of existing finite gadgets together with this symmetry;
it is not a newly found displacement-16 insertion preserving the old local
window. T_p need not preserve H4,L0,H0,L1, so it is applied only AFTER all
window-dependent insertions and BEFORE depth-preserving appends.

## 3. Universal reflected-displacement lemma

Use a compatible core with endpoints H3,L(p-4), window H4,L0,H0,L1, and
its maximum pair entirely BEFORE L0. Let z be the zero-based index of L0.
The accepted insertion of size q is

    P ++ (q+C[:z]) ++ B ++ [0,0] ++ D ++ (q+C[z+2:]).

Here old positive entries shift by q, while the two zeros remain fixed;
P,B,D are positive and have even lengths. An old maximum p-1 becomes
p+q-1, strictly greater than every new gadget entry 1,...,q. Its pair
remains adjacent, remains before L0, and its first index becomes t+len(P).
No assumption about where the other old entries lie is needed.

The final reverse-complement pair start therefore changes by

    [2(p+q)-1-(t+len(P))] - [2p-1-t] = 2q-len(P).

Thus maximizing the original zero displacement len(P)+len(B) is a DIFFERENT
optimization from maximizing reflected displacement 2q-len(P).

We use only two inherited q9 gadgets from the frozen q18 predecessor data:

    original delta4:
    P=[3,6]
    B=[9,4]
    D=[1,1,2,5,3,2,4,6,5,7,7,8,8,9]

    original delta6:
    P=[3,5,6,6]
    B=[9,4]
    D=[1,1,2,5,4,2,3,7,7,8,8,9]

Their reflected displacements are 16 and 14 respectively. The finite
certificates have each H side and L side exactly 1,...,9, the prescribed
endpoints, and replacement-chain sums [1,19] union {22}. To see universal
sufficiency directly, retained sums are {0} union ([20,2p+16] minus {22});
the replacement chains P,H12; H13,B,L0; H0,D,L10 fill precisely the
complement. The new core has size p+9 and the same insertion contract.
This argument is independent of solver statuses and p.

After j steps, choose t of the delta4 gadgets and j-t of the delta6 gadgets.
The reflected pair starts at b+14j+2t. Any order works, since the maximum
pair stays before zero throughout. For t=0,...,j and both adjacent depths,
the complete attainable depth set contains the integer interval

    [b+14j, b+16j+1].

The extreme rate is 16 added depths per 18 added arm positions, namely 8/9.
The q18 gadget's prefix length4 would give 32/36=8/9 by the same argument,
but q9 alone gives all intermediate displacements and suffices here.

## 4. Six old seeds, both orientations and every size residue

The six literals in data.json are exact copies from the accepted 48-seed
bank, identified by its (p, original low-zero depth) key. No seed search was
performed in this task. The table records one-based OLD maximum positions.

| p | old zero depth | old maximum pair | reflected pair depths |
|---|---:|---:|---:|
| 16 | 16 | 6,7 | 26,27 (L0,H0) |
| 17 | 22 | 8,9 | 26,27 (L0,H0) |
| 18 | 22 | 10,11 | 26,27 (L0,H0) |
| 19 | 20 | 12,13 | 26,27 (L0,H0) |
| 20 | 24 | 16,17 | 24,25 (L0,H0) |
| 21 | 22 | 15,16 | 27,28 (H0,L0) |

In every row the maximum pair is entirely before the old zero pair.
For fixed j>=1, intersecting the six full DEPTH intervals from section 3
gives

    J_j=[27+14j,25+16j].

This is nonempty because its upper minus lower is 2j-2. It is already a
depth interval including the extra neighbor of each pair; adding another
one to its common upper endpoint would be incorrect. J_1={41}, and
J_2=[55,57]. The p21 odd-start pair is essential to the exact lower endpoint.

At any target size p>=16+9j, divide

    p-(16+9j)=6r+delta, r>=0, 0<=delta<=5.

Choose the table seed of size p0=16+delta; perform j insertions; apply
T_(p0+9j); then append r translated copies of

    C6=[3,3,2,1,1,0,0,4,4,5,5,2].

At current size x, this appended block adds x,...,x+5 to each side. Its
internal sums are [2x,2x+10], and its bridge to old endpoint L(x-4) is
(x-4)+(x+3)=2x-1. The new endpoint is L(x+2)=L((x+6)-4).
All appended entries are positive and all old positions are unchanged.
It therefore preserves both NEW zero positions. Appending before T is
invalid for this purpose: it changes the maximum pair that T turns into
zeros. That false interchange is explicitly tested as a negative control.

This proves that every depth of J_j is available at every p>=16+9j,
including all six residues. It is an unbounded division-and-identity proof.

## 5. Joining the accepted prefix and both parity shells

For p>=25 put U=floor((p-16)/9)>=1. At this target size the accepted D5
prefix runs through 27+14U+2floor(U/2), and section 4 supplies
J_U=[27+14U,25+16U]. Their overlap is nonempty. Moreover,

    (25+16U)-(27+14U+2floor(U/2))
      = 2U-2floor(U/2)-2 >=0.

The union is thus the entire prefix 2,...,25+16U. Smaller p retain D5.
No overlap between different J_j intervals is required.

Both accepted shell lemmas require ONLY a balanced core with endpoints
H3,L(p-4). They do not require the old four-vertex insertion window.
For completeness their explicit maps are reproduced here. Put M=2k.

Odd shell k=2p+3, center/cut A=k-1:

    selected = (M-c0,c1,M-c2,c3,...) ++ [3p+3,p+1,3p+4],
    partner  = concat_i=0..p-1 (2p+3+i,2p+1-i) ++ [3p+6,p,3p+5].

Even shell k=2p+4, center/cut A=k:

    selected = (M-c0,c1,M-c2,c3,...) ++ [3p+5,p+2,3p+7,p+3],
    partner  = concat_i=0..p-1 (2p+5+i,2p+3-i) ++ [3p+6,p,3p+8,p+1].

These two k-arm paths plus the center use labels [0,M], differences [1,M]
once and cross A on every edge, by the accepted band-partition proofs.
For h=n-2, Q=hk+m, raise every high path label by Q. Label the residual
long arms i=0,...,h-1 at depth t by

    A+(h-i)k-(t-1)/2     when t odd,
    A+ik+t/2            when t even,

and the short leaves A+hk+1,...,A+hk+m. These residual labels fill
[A+1,A+Q]; their differences fill [1,Q]. Each alpha path edge difference
increases by Q, filling [Q+1,Q+M]. Labels fill [0,nk+m] exactly.

The low core zero remains zero, and the high zero becomes nk+m. Global
complementation sends the latter to zero and preserves all differences.
This handles both table orientations. Assign the selected and partner paths
to any chosen distinct arms; it includes n=2,m=0 with Q=0 and arbitrary m.

For odd k=2p+3 and even k=2p+4,

    floor((p-16)/9)=floor((k-35)/18).

For even k, the numerator k-36 is even and adding one cannot cross a
multiple of 18. Thus the same displayed all-k theorem follows. For k>=53
write k=35+18U+s, 0<=s<=17. Then

    8k-9D_rc(k)=55+8s in [55,191].

At 19..34 the deficit is 8k-99 in [53,173]; at 35..52 it is 8k-243 in
[37,173]. This proves the global ratio bound and the limit.

## 6. Executable evidence and frozen boundary

prepare.py copies selected finite certificates and hashes sources.
construct.py produces literal core and actual named-spider certificates.
check.py imports neither constructor, predecessor code nor any solver. It
checks side permutations, sums, all supplied actual vertex/edge multisets,
BFS distances, the precise zero, finite gadget identities, residue and interval
arithmetic, and deliberately false alternatives. The universal proof is
sections 2--5, not extrapolation from finite output.

Normal and optimized runs both PASS with identical results:

* 6 inherited seeds with both reflected-pair orientations;
* 2 complete q9 missing-sum identities;
* 748 generated cores and 1,760 actual named spiders;
* 1,000 target-size arithmetic checks and 240 exact interval checks;
* 8 rejected negative controls, including wrong complement constant, wrong
  target, wrong shell length, a duplicate graph label, the false assumption
  that every reflected pair starts low, and append-before-reflect.

Core certificates cover every new common-window depth at p=25,...,106.
Actual-spider certificates use both k=2p+3,2p+4, (n,m)=(2,0),(3,0),(3,2),(5,1),
arms 0,n-1, and the explicit target-size list in construct.py. U=1,2,3 and
all residues occur. check.py additionally checks p=25,...,1024 arithmetically.
This checker was developed in the author task and is internal executable
corroboration; it is not a separate-agent audit or a proof assistant.

Reproduce in a writable copy with Python standard library:

    python -B construct.py
    python -B check.py
    python -B -O check.py

The exact result files, source-inputs.json, manifest.json and SHA256SUMS.txt
bind the private package. RESTART is recorded as mutable context and excluded
from proof-dependency drift checks. Original mathematical sources are checked
for unchanged hashes. No q24 case or additional spider search was run.

## 7. Primary overlap and scientific limits

This is a project-level strengthening obtained from inherited q9 gadgets,
six already accepted seeds, a reverse-complement symmetry, C6 append and
the accepted two parity shells. The finite gadgets and seeds are not newly
discovered here. Reversal, complementation, balanced path endpoints and
alpha amalgamation are established ingredients and must not be presented
as new inventions.

The read-only bounded primary comparisons in source-inputs.json record
exact older endpoint overlap through Kotzig-attributed Ollis Lemma 5.5,
older path/alpha-complement/concatenation machinery, and full overlap for
n=2,m<=1. Cattell's full path/alpha characterization and original
Kotzig/Rosa proofs remain incompletely accessed in that record. No new
primary-source search was performed here. This report does not upgrade
those inherited comparisons into a literature non-subsumption finding.
Worldwide priority and historical novelty remain UNKNOWN; reversal and
alpha-complement make that comparison especially necessary.

The q24 eight delta42 cases remain UNKNOWN and unchanged. Pendant interval,
three-tail and endpoint-padding no-go statements keep their exact restricted
scope. None is contradicted: this construction uses the existing two-arm
alpha shell and modifies the core. Missing near-tip interior depths for
all n,m remain UNKNOWN. The method supplies neither a full all-length
zero-rotatability theorem nor an external review.

**Decision:** freeze this positive candidate and request separate internal
reconstruction of the exact theorem, especially both pair orientations,
residue completion, U=1/2 seams, append order and even-shell transfer. No
publication follows from the author checker. A next falsifiable target is
a compatible insertion with shorter prefix relative to q, since the
reflected rate is 1-len(P)/(2q); that is a separate research cycle.
