# Separate internal audit: positive q10 and q11 two-entry-prefix gadgets

Private mathematical audit, 9 October 2026. **GO for both exact literal gadgets,
their universal compatible-core insertion identities, arbitrary iteration, and
the conditional reflected tracked-pair gains18 and20.** No all-k prefix,
residue coverage, optimality, historical priority, external review or Lean proof
is inferred. Earlier q10/q11 UNKNOWN records were correct when frozen and
remain unchanged. No shared checkpoint, author artifact, site or CMS was edited.

## Exact source binding

Author package: research-audits/graceful-q10-q11-p2-frontier-private-2026-10-09.

| Artifact | SHA256 |
|---|---|
| report.md | b6afd14b14d05344830fae350a0b170d6e6bfc1b2c341de57141d82d24465666 |
| manifest.json | 00bde290bd400619849c1a907bf0ad9b10972c2256fe575a0cb6fb8c11fab0af |

The auditor's checker verifies both fixed bindings and all six manifest payload
hashes and sizes before and after the checks. The exact report and manifest are
copied into inputs/. Neither the author search nor checker is imported or run.
Search statuses and the auxiliary q11/x9 exclusion are not acceptance premises.
The six larger example cores in inputs/seed-data.json are copied from the
accepted reflected-core package and checked as integer literals before use.

## 1. Exact tagged and sum partitions

For q10 the positive certificate is

    P=[3,8], B=[10,8,9,10,5,5,4,2,3,4],
    D=[1,1,2,6,6,7,7,9].

P starts H and alternates H,L. B,D start L and alternate L,H. Their H-side
lists together are [3,8,10,5,2,4,1,6,7,9]; their L-side lists together are
[8,10,9,5,4,3,1,2,6,7]. Each is exactly a permutation of1,...,10.
The three chains P,H13; H14,B,L0; H0,D,L11 have weight lists

    11,21;
    24,18,17,19,15,10,9,6,5,7,4;
    1,2,3,8,12,13,14,16,20.

They partition [1,21] union {24}. Lengths are2,10,8; P starts H3,
B ends H4 and D starts L1. These exact arithmetic identities prove the
gadget independently of the search which found it.

For q11 the positive certificate is

    P=[3,8], B=[11,10,5,5,4,2,3,4],
    D=[1,1,2,6,6,7,7,9,10,8,9,11].

Its H-side lists together are [3,10,5,2,4,1,6,7,9,8,11]; its L-side lists
are [8,11,5,4,3,1,2,6,7,10,9]. Both permute1,...,11. The chains
P,H14; H15,B,L0; H0,D,L12 have weight lists

    11,22;
    26,21,15,10,9,6,5,7,4;
    1,2,3,8,12,13,14,16,19,18,17,20,23.

They partition [1,23] union {26}. Lengths are2,8,12 and the required
endpoint values hold. Here the D boundary supplies23 and the P boundary22;
both top-sum providers are necessary. The q>=12 obstruction does not apply.

## 2. Universal all-p insertion reconstructed

Let C be ANY compatible balanced core: alternating H,L, length2p, each side
permuting0,...,p-1, sums0,...,2p-2 once each, endpoints H3,L(p-4), and
window H4,L0,H0,L1. These hypotheses imply p>=6. At p<=4 H4 is absent.
At p5 the endpoint is L1, already adjacent to H0 and having degree1;
the window saturates H0 and L0, so none of H1-L1,H2-L0,H0-L2 can supply
required sum2. Thus there is no compatible p5 core.

Write z for the odd zero-based index of L0. For either q in{10,11}, form

    C'=P ++ (q+C[:z]) ++ B ++ [0,0] ++ D ++ (q+C[z+2:]).

Every entry in the old prefix/suffix is positive. On either tag, the new
entries supply1,...,q, the old positive entries become q+1,...,p+q-1,
and the one old zero remains0. These three bands partition0,...,p+q-1.
The even block lengths preserve alternation. The first entry remains H3;
the final old entry becomes L(p+q-4). B's final H4, the zero pair and D's
first L1 retain exactly the same compatible window. The new size is p+q.

Only old H4-L0 and H0-L1 edges, with sums4 and1, are removed. The
old zero-zero edge remains0. All other retained edges join positive values,
so each old sum increases by2q. Thus retained sums are precisely

    {0} union ([2q+2,2p+2q-2] minus {2q+4}).

The three replacement chains verified above provide precisely
[1,2q+1] union {2q+4}. The sets are disjoint and partition
0,...,2(p+q)-2. This proves the full core identity for every compatible C,
not a finite seed extrapolation. Because endpoints and window persist, any
finite word of q10/q11 insertions can be applied repeatedly.

The old low-zero index z changes by len(P)+len(B):12 for q10 and10
for q11. These are the ORDINARY window shifts. They are not18 or20.

## 3. Reflected gains, with their exact extra hypothesis

Suppose the adjacent old maximum pair p-1,p-1 starts at zero-based index t
and lies entirely before L0: t+1<z. Both members are positive, so insertion
makes them p+q-1. They remain adjacent and precede the new zero window;
their new first index is t+len(P)=t+2. They are the unique new maximum
pair because all fresh entries are at most q<p+q-1.

For any balanced endpoint-compatible core, define

    T_p(C)[i]=p-1-C[2p-1-i].

Reversal swaps tag sides; complementation permutes their ranges. Consecutive
sums become2p-2-s, and endpoints become H3,L(p-4). Hence T preserves
the balanced shell contract. It may lose the insertion window, so apply it
after all window-dependent insertions. Its maximum pair becomes the zero
pair at one-based selected-arm depths b=2p-1-t and b+1.

After a q insertion, the new reflected start is

    2(p+q)-1-(t+2)=b+(2q-2).

Therefore the exact reflected gains are **18 for q10** and **20 for q11**.
The before-zero hypothesis survives every insertion, so these gains add
for arbitrary finite mixed words before the final reflection. This statement
does not assert contiguous depths at every size or an all-k prefix. The rates
18/20 and20/22 are positional ratios for these moves, not completed all-k
coverage theorems in this audit.

## 4. Actual-spider transport and executable evidence

The reflected core retains H3,L(p-4), both tagged permutations and all sums.
It therefore satisfies the accepted odd shell k=2p+3 and even shell k=2p+4
contracts. The two numeric zeros become the label0 and path maximum2k at
those same core depths. Each shell is a two-arm alpha path with midpoint cut
A=k-1 for odd k and A=k for even k.

For arbitrary n>=2,m>=0 and any selected arm choose a distinct partner.
Let h=n-2,Q=hk+m,N=nk+m. Label the residual spider center0, its arm i at
odd depth2u+1 by (h-i)k-u and at even depth2u by ik+u; give short leaves
hk+1,...,Q. Blockwise side partitions give labels0,...,Q; center multiples
of k and internal open k-blocks give weights1,...,Q. Shift residual labels
by A and path labels above A by Q. The full label partition is
[0,A-1], [A,A+Q], [A+Q+1,N], meeting at the one identified center.
Residual weights remain[1,Q]; every path weight increases by Q, supplying
[Q+1,N]. Complement the entire graph when the requested zero-pair member
carries N. The named selected arm and its actual center distance are preserved.
This is the inherited actual-spider transfer; it does not supply missing
residue or contiguous-prefix coverage.

The separate checker implements literal core checks, insertion, reflection,
both shell formulas and the final named graph directly, importing no predecessor
constructor/checker or solver. It checks the p6 boundary literal

    [3,4,2,3,5,5,4,0,0,1,1,2]

and six larger literal compatible cores at p16,...,21. For each it follows
q10-only, q11-only and alternating q10/q11 words at0,...,5 steps. It checks
126 iterated cores,126 reflected cores, and4032 actual spiders: both shell
parities; n2/3; m0/7; both named selected arms; both adjacent zero depths.
Complete label/weight Counters and BFS check the target vertex, including
n2,m0. This finite matrix diagnoses transcription; the partitions above
carry every compatible p and the unbounded n,m quantifiers.

Nine negative controls reject altered P, D and B anchors/entries for both
gadgets, premature reflection followed by the window-dependent contract,
a changed core endpoint, and confusion of ordinary shift12 with reflected
gain18. Normal/-O outputs are byte-identical PASS and source hashes remain
unchanged. Reproduce with

    python -B independent_check.py
    python -B -O independent_check.py

## Verdict

**GO** for the two literals, universal compatible insertion and iteration,
conditional tracked-pair reflection gains18 and20, and inherited actual-spider
transport under its exact shell contracts. No reported mathematical defect was
found. This resolves q10/q11 P2 positivity through new evidence; it does not
rewrite the correct earlier UNKNOWN snapshots.

**UNKNOWN here:** an all-k prefix, residue/coverage proof, optimal slope, full
zero-rotatability, unrestricted near-tip existence, historical priority and
external review. The earlier q>=12 P2 NO-GO retains its exact restricted scope.

Jordi Gartner publishes through Beedbyte. AI assistance in this private audit
supplied separate proof reconstruction, direct certificate/core/spider checks
and reporting. This is an internal project check, not a public release.
