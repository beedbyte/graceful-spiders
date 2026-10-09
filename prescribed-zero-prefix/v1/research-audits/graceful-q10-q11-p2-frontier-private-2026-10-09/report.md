# Private q10 and q11 P2 insertion frontier

9 October 2026. Separate internal mathematical search and executable check.
Both q10 and q11 are POSITIVE in the exact compatible H4,L0,H0,L1 interface.
Historical inputs and prior UNKNOWN records remain unchanged. No public release,
external review, formal proof-system verification or novelty claim is made.

## Exact finite contract and necessary constraints

P,B,D are nonempty even lists totaling 2q entries. P starts H, B,D start L;
combined H entries and combined L entries each permute 1,...,q. P starts H3,
B ends H4, D starts L1. Their chains are exactly

    P,H(q+3); H(q+4),B,L0; H0,D,L(q+1).

The 2q+2 edges must supply [1,2q+1] union {2q+4} once each. With P2,
write P=[3,x]. Every internal edge is at most 2q. Exceptional sum2q+4
forces B first Lq: the P boundary is at most2q+3, D boundary at most2q+1.
Sum2q+1 is supplied by P boundary (x=q-2) or D boundary (D last Hq).
In the latter case sum2q can only come from P boundary (x=q-3), Hq-Lq,
or D boundary H(q-1). The last possibility conflicts with the forced Hq;
Hq-Lq joins B's and D's disjoint vertices and is impossible. Thus
x belongs to {q-2,q-3}. Both providers of sum2q+1 have been retained.
For x=q-2, D last cannot be Hq because that would duplicate sum2q+1;
for x=q-3, D last must be Hq.

Sum1 is H0-L1; sum4 is H4-L0. Since x>=7 here, P cannot supply sums2
or3. Sum2 forces H1-L1 and sum3 then forces H1-L2. Consequently D2
is impossible: it would terminate at H1 and saturate it with the old
L(q+1) boundary, preventing sum3. Hence B>=2, D>=4, B+D=2q-2.
The seven q10 allocations are B=2,4,...,14 with D=18-B; the eight q11
allocations are B=2,4,...,16 with D=20-B. Direct zero-window displacement
is 2+B. The finite domains are exactly fresh indices1..q and the four
displayed old boundary vertices; no ordering or split symmetry is imposed.

The new search assigns edges by increasing required weight with exact tagged
degrees, rejects cycles and joins of the wrong endpoint pair, and allows every
B/D allocation simultaneously. It imports no earlier research constructor or
solver. It explores 22 nodes to the chosen q10 x8 witness and 31 nodes to the
chosen q11 x8 witness. The saved other branches are auxiliary: q10 x7 also SAT;
q11 x9 exhausts at19 nodes without a witness. Positivity of each q does not
depend on that auxiliary UNSAT branch or on trusting search statuses.

## q10 literal positive certificate

    P=[3,8]
    B=[10,8,9,10,5,5,4,2,3,4]
    D=[1,1,2,6,6,7,7,9]

Lengths are2,10,8. Chain sums, in their actual path orders, are

    P: 11,21
    B: 24,18,17,19,15,10,9,6,5,7,4
    D: 1,2,3,8,12,13,14,16,20.

Their union is [1,21] union {24}. Tagged side lists each permute1..10.
The ordinary compatible-core zero pair shifts12 positions.

## q11 literal positive certificate

    P=[3,8]
    B=[11,10,5,5,4,2,3,4]
    D=[1,1,2,6,6,7,7,9,10,8,9,11]

Lengths are2,8,12. Chain sums are

    P: 11,22
    B: 26,21,15,10,9,6,5,7,4
    D: 1,2,3,8,12,13,14,16,19,18,17,20,23.

Their union is [1,23] union {26}. Tagged side lists each permute1..11.
The ordinary compatible-core zero pair shifts10 positions. Here D's final
H11 supplies23; the prefix boundary supplies22. This is why omitting the
second top-sum provider would incorrectly lose the q11 witness.

## Universal insertion identity

Assume any compatible size p core C: it alternates H,L, each side permutes
0,...,p-1, its2p-1 edge sums permute0,...,2p-2, its first and last entries
are H3 and L(p-4), and it contains the consecutive window H4,L0,H0,L1.
These hypotheses imply p>=6. Write C=U,H4,L0,H0,L1,V.
Apply f(0)=0 and f(v)=v+q to all old values and form

    C'=P,f(U),H(q+4),B,L0,H0,D,L(q+1),f(V).

Here f(U) includes all old prefix entries before H4. If U is empty the
old first-H3 requirement would contradict H4; the displayed prefix connection
is therefore always P,H(q+3), as required.

Alternation is preserved because every insertion block is even. The sides
each contain0, fresh1..q, and shifted old positives q+1..p+q-1, so each
side permutes0..p+q-1 exactly. The first entry is H3; the last is
L(p+q-4). The window H4,L0,H0,L1 occurs at the end of B and start of D.
Only two old edges are removed: H4-L0 (sum4) and H0-L1 (sum1).
The H0-L0 edge remains sum0. All other retained edges have both endpoints
positive, hence their sums increase by2q. Their set is precisely

    {0} union ([2q+2,2p+2q-2] minus {2q+4}).

The prefix and two replacement chains have sums [1,2q+1] union {2q+4}
by the literal certificates above. These sets are disjoint and partition
0,...,2(p+q)-2. This proves the identity for EVERY compatible core; finite
iteration tests are supplementary. The new window starts len(P)+len(B)
positions after its old start; endpoints and window are retained for iteration.

The previously established reflected construction arithmetic would associate
P2 with zero-pair displacement2q-2:18 at q10 and20 at q11, giving possible
rates9/10 and10/11. This package does not prove an all-k prefix: compatible
seed coverage, residue classes, shell/reflection transport and prefix gaps
must be supplied in a separate argument. The ordinary displacements above
are12 and10 and must not be confused with the reflected displacement.

## Checks, provenance and frozen scope

check.py imports neither search.py nor a solver. Its literal certificates check
every side occurrence, alternating chain endpoint and edge sum. It checks the
q9 frozen compatible p6 seed and30 iterated insertions per q, reconstructing
side sets, edge sums, endpoints, window and displacement each time. Normal and
optimized Python output match exactly. All13 negative controls fail explicitly:
five corruptions plus truncation for each gadget, and a wrong core endpoint.
The checker uses exceptions, so -O does not remove checks. The root chat also
reported a separate literal arithmetic check of both candidates and splits.

The finite q9 seed is [3,4,2,3,5,5,4,0,0,1,1,2] from the frozen provisional
q9 search results; it is independently verified before use. It is used solely
for executable illustrations. It is not a residue/seed coverage theorem.

Run python -B check.py and python -B -O check.py; both are read-only.
search.py recreates results.json, so reproduce the search in a writable copy.
manifest.json freezes local artifacts and exact read-only input hashes.
Only this private directory was written; no shared checkpoint, CMS, site,
profile, q24 search or historical source was changed.
