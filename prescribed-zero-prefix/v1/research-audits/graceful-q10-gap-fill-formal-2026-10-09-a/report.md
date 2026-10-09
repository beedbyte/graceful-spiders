# Formal D8 q10 gap completion through all integer lengths

Private internal formal record, 9 October 2026. **Formal GO for the scoped D8
actual-spider prefix, universal q10 insertion/tracking, finite recipes,
unbounded translation, monotonicity, nonregression and integer ratio criterion
below, supported by the final clean build and verification records.** Separate
copied-source replay is pending at freeze. No public release, external review,
peer review, worldwide priority, graph-theoretic optimum or full
zero-rotatability is claimed.

Jordi Gartner publishes this work through Beedbyte. AI assistance in this private
task supported formal interface/proof development, exact literal and source
binding, compilation and internal checks. Bound mathematical audits are
internal project checks, not external review or Lean assumptions. Historical
priority remains UNKNOWN. D7 and all earlier frozen bytes remain unchanged.

## Exact theorem and graph contract

For every integer k>=19 define

    D8(k)=D7(k)                                    if k<=124,
    D8(k)=107+20a+2r                               if k>=125,
    p=floor((k-3)/2), a=floor((p-61)/11), r=(p-61) mod11.

In the high branch p>=61 and 0<=r<=10. D7 is the exact copied predecessor
function. `GracefulBoundary.GapFill.all_lengths_prefix_zero` proves:

```lean
theorem all_lengths_prefix_zero (k n m d : Nat) (hk : 19≤k)
    (hn : 2≤n) (a : Fin n) (hd : 2≤d ∧ d≤depthPrefix k) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0
```

This is the exact inherited indexed S(k^n,1^m), with its center, long arms,
short leaves and actual edges. `Graceful` requires complete bijections onto
vertex labels0,...,n*k+m and absolute edge differences1,...,n*k+m. One-based
depth d is represented by d-1. There is no parity restriction, finite upper
bound or m>=1 hypothesis. All chosen arms a, n>=2 and m>=0 are quantified,
including n2,m0. Different requested vertices may use different labelings.
The legal target bound is returned, and `prefix_inside` proves D8(k)<k.

## Universal q10 insertion and tracking

Q10Gadget.lean embeds the exact accepted q10 P2 certificate

    P=[3,8], B=[10,8,9,10,5,5,4,2,3,4],
    D=[1,1,2,6,6,7,7,9].

Ordinary kernel `decide` proves the finite side and chain certificates. Fresh
H offsets and L offsets each permute1,...,10. The replacement chains
P,H13; H14,B,L0; H0,D,L11 have sums[1,21] union{24}. Their lengths are2,10,8,
and their required endpoints and parity hold. The chosen literal is compared
with the frozen q10 author's x8 certificate; auxiliary search statuses and the
other positive q10 branch are not proof premises.

Q10Core.lean proves `q10_preserves_invariant` for every supplied
`Variable.AnchoredCore p d c`. Positive old entries shift by10, zeros remain
zero, size grows by10, and retained positive sums shift by20. The proved fresh
chains fill the removed sums1,4 and the prefix connection. Both side ranges,
the complete sum range, H3/L(p+10-4) endpoints, legal anchor and
H4,L0,H0,L1 window persist. The ordinary low-zero anchor shift is12.

Q10Tracking.lean proves exact prefix lookup and maximum-pair preservation. The
tracked old pair lies wholly before L0, its values become p+10-1, its first
index increases by len(P)=2, and it remains before the new window.
`source_step` therefore proves reflected first-depth gain20-2=18;
`source_iterate` proves size10b/depth18b for every nonnegative iteration count.
These are universal results, with no finite upper bound on the source size.

The copied D6 symmetry and D7 q11 source lemmas supply reverse-complement,
both oriented CorePair conversions and size11a/depth20a. The new reflected
core is formed only after all compatible insertions. No insertion is applied
to an already reflected core.

## Seven kernel-checked recipes and all residues

GapRecipes.lean uses the two exact copied compatible seeds of size16 and17,
whose original tracked-pair proofs are inherited and whose reflected first
depth is26. Their literal arrays are compared with the D8 author seeds.json.
A recipe records delta in{0,1} and counts(c,b,a) of q9 P2, q10 P2 and q11 P2.
`recipe_coverage` constructs a source of size

    p=16+delta+9c+10b+11a

and reflected depths26+16c+18b+20a and its following depth. The formal order
is q9, then q10, then q11, followed by a single final reverse-complement.
Every step retains the tracked compatibility contract. No new C6 append is
needed for these gap recipes.

| p | seed | q9 | q10 | q11 | depths |
|---|---:|---:|---:|---:|---|
|62|16|4|1|0|108,109|
|64|16|3|1|1|112,113|
|66|16|2|1|2|116,117|
|68|16|1|1|3|120,121|
|70|16|0|1|4|124,125|
|71|17|0|1|4|124,125|
|71|16|0|0|5|126,127|

`finite_gap_cover` proves, by kernel `decide`, coverage of every integer in
[F7(p)+1,F8(p)] for all eleven p61..71 cases. Five cases have an empty gap;
the other six use the seven exact recipe literals. The finite predicate
evaluates every requested depth and requires a recipe satisfying the full
size and pair-depth contract. `finite_gap_recipe` extracts the witness and
the universal recipe theorem supplies its core. This is not a Python
existence premise. `recipe-identities.json` compares every literal count and
target pair with the exact frozen recipes.json. Both rows at p71 are used;
the isolated upper pair alone is not treated as interval coverage.

For arbitrary p>=61, divide p=p0+11t with61<=p0<=71. The copied F7 shift
lemma and new F8 shift lemma prove both endpoints increase by20t. `valid_lift`
adds t q11 moves to the witness recipe BEFORE reflection, increasing size11t
and both depths20t. `gap_coverage` thus fills every new gap at every p, without
a finite horizon or omitted residue. `all_depth_core_coverage` uses the
inherited D7 core theorem through F7(p) and the new recipe theorem above it,
giving the full core prefix2,...,F8(p).

GapDepth.lean applies the copied, freshly rebuilt exact odd/even core-spider
transfer at p=floor((k-3)/2). Those shells require the balanced endpoints and
zero/max offsets, not a preserved insertion window. Residual labeling,
midpoint graft identification, arbitrary-arm permutation and complementation
of the entire spider are inherited kernel-proved sources. The final D8 theorem
has no supplied core, residual proof, parity premise or graph-isomorphism
assumption.

## Comparison and quantitative statements

`F_dominates_D7` proves F8>=F7 from their formulas; `prefix_dominates_D7` proves
D8>=D7 pointwise. `F_monotone` proves the high-branch monotonicity and
`prefix_monotone` includes the k124/125 seam. At r10 to the next r0, F8 stays
constant; the proof does not assume strict increase everywhere.

`tail_error_bound` proves, for every k>=125,

    11D8(k)<=10k,          53<=10k-11D8(k)<=83.

`prefix_error_bound` proves for every integer k>=19

    11D8(k)<=10k,          10k-11D8(k)<=261.

The first inequality prevents natural subtraction from masking a negative
error. The low branch uses the exact inherited D7 bound. The sufficient
limiting fraction remains10/11; this extension adds bounded depths rather
than improving that fraction.

`prefix_ratio_precision_limit` proves the unbounded integer criterion

    forall precision:Nat, exists cutoff:Nat, forall k>=cutoff,
      precision * distance(11D8(k),10k) < k,

with cutoff=262*precision+19. The ordinary real-ratio interpretation gives an
error at most261/(11k) from10/11. A literal Lean `Real`/topological `Tendsto`
theorem or formal equivalence to that criterion is not included. A K8 exact
inverse and maximality within an expanded recipe family are not formalized;
verification records each limitation separately.

## Exact inputs, build and trust boundary

The frozen D7 manifest is
`76022dcd140c9a989040d7c25e8ed597336d0971739066ad95e7983c129bdcec`.
All51 copied proof modules are byte-identical. Its frozen objects are not final
imports. The q10/q11 author manifest is
`00bde290bd400619849c1a907bf0ad9b10972c2256fe575a0cb6fb8c11fab0af`, and its
separate gadget audit manifest is
`720ef06b23bf2a7a5cc39dd02d260f519ac0939ad58e69be73f747ebe1ef4afd`.

The D8 author report/manifest SHA-256 bindings are
`3150df1b1f6296c580eebf5c2bc4b7bba9b6ae97436b0ebfbb821f70c41658a6` /
`ce41485e485b6dd86c92092923326fdaa47095fa8243eb4d733c4531d5d5b685`.
The separate D8 mathematical audit bindings are
`b9886f996b045aea344b4f62d3f6344801fa481024d943283b2fe5a7456f5c15` /
`42e6eb15ccb557b6f81b5addd1db2cd69ee5c394d42b50356a66422e5272e262`.
Snapshots, source-copy identities and full frozen manifest payload inventories
are retained in inputs/, input-bindings.json and frozen-inputs.json. All bound
original payloads are checked before/after the build and by final verification.
No original author checker, search or solver was run or edited.

The five new proof modules are Q10Gadget, Q10Core, Q10Tracking, GapRecipes and
GapDepth. The57th source is GapAudit. The final build rebuilds every source in
the previously absent build-final with `-DwarningAsError=true`; all exit codes
are zero. Exact compiler-call timing, command arguments, logs and before/after
source identities are in the build protocol and verification.json. LEAN_PATH
contains only this fresh object directory. Development objects supply no final
imports.

All706 named source theorem `#print axioms` outputs are present. Complete
inventories are theorem-inventory.json and axiom-inventory.json. The sole union
is `propext`, `Classical.choice`, `Quot.sound`; no added mathematical axiom or
sorryAx occurs. The comment/string-aware lexical screen finds no sorry, admit,
native_decide, sorryAx, axiom declaration or unsafe declaration. Std is the sole
external source import. source-hashes.json lists every compiled source hash.

Lean is4.34.0, Windows x86_64 release commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, compiler SHA-256
`a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`.
The Lean kernel/compiler and installed Std implementation remain trusted; they
were not independently rebuilt or externally certified. Correctness is relative
to that toolchain, the explicit graph definitions and standard axioms. Python
identity and lexical checks are diagnostic/provenance gates, not Lean premises.

## Freeze and reproduction

verify_final.py checks complete build coverage, all706 axiom reports, exact
sources/inputs/toolchain, the q10 literal, seven recipes and two seed arrays.
Its saved status is
`GO_FORMAL_D8_ALL_INTEGER_LENGTHS_GAP_FILLED_PREFIX_AND_INTEGER_RATIO`.
After freeze it compares saved evidence and every local manifest entry without
rewriting them or compiling frozen sources. SHA256SUMS.txt binds all local
files except itself. Temporary generation scripts are not reproduction inputs.

For a separate fresh copied-source replay, copy the package elsewhere and run
`python -B build.py --build build-replay` there, then compare source and axiom
identities. Never compile or regenerate inside the frozen package. Separate
replay remains pending at freeze. No public CMS/site/profile, published revision,
shared RESTART or cycle file was written. Global optimality, full zero-rotatability,
remaining near-tip depths, unequal arm lengths and historical novelty remain
outside this formal scope.
