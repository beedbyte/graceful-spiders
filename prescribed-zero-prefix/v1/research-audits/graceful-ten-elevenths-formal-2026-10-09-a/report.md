# Formal all-integer D7 prescribed-zero prefix

Private internal formal record, 9 October 2026. **Formal GO for the exact
actual-spider D7 prefix, q11/core recipe construction, nonregression,
monotonicity, exact inverse K7 and quantitative integer ratio criterion below.**
All 52 source modules pass a fresh warnings-as-errors build; all 658 named
source theorem axiom reports are complete. Separate copied-source replay is
pending at freeze. No public release, external review, peer review, historical
novelty, full zero-rotatability or graph-theoretic optimum is claimed.

Jordi Gartner publishes this work through Beedbyte. AI assistance in this
private task supported formal proof development, exact source and recipe
binding, compilation and internal checks. The separately bound mathematical
audits are internal project checks and are not Lean premises or external review.
Historical priority remains UNKNOWN. D5/D6 frozen records are unchanged.

## Exact theorem scope

For all integers k>=19, put p=floor((k-3)/2). Define

    D7(k)=D6(k)                              at k<=124,
    D7(k)=F(p)                               at k>=125,
    F(p)=107+20a+4 floor(min(r,9)/2),
    a=floor((p-61)/11), r=(p-61) mod11.

The inherited D6 is 11 at k19..34, 27 at k35..52 and
25+16floor((k-35)/18) thereafter. For p>=61, r lies in0..10, with within-block
increments [0,0,4,4,8,8,12,12,16,16,16].

`GracefulBoundary.Q11.all_lengths_prefix_zero` proves:

```lean
theorem all_lengths_prefix_zero (k n m d : Nat) (hk : 19≤k)
    (hn : 2≤n) (a : Fin n) (hd : 2≤d ∧ d≤depthPrefix k) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0
```

The conclusion targets the inherited exact indexed S(k^n,1^m), including its
center, long-arm and short-leaf vertices and actual edges. `Graceful` requires
full bijections onto vertex labels0,...,n*k+m and actual absolute edge
differences1,...,n*k+m. One-based depth d is represented by d-1. There is no
parity premise and no finite upper bound on k,n,m or d. Every selected arm is
quantified, and m0 and n2,m0 are included. Labelings may depend on the requested
vertex. The theorem returns the legal-vertex bound; `prefix_inside` separately
proves D7(k)<k.

## Universal q11 insertion and tracked pair

Q11Gadget.lean embeds the exact inherited positive certificate

    P=[3,8], B=[11,10,5,5,4,2,3,4],
    D=[1,1,2,6,6,7,7,9,10,8,9,11].

Ordinary kernel `decide` proves its side and chain certificates. Each tagged
side supplies1,...,11; the replacement chains P,H14; H15,B,L0; H0,D,L12 have
sums [1,23] union{26}, with the required endpoints and even block lengths.
The literal arrays are compared exactly with the frozen q11 author results.
Search statuses and excluded auxiliary branches are not Lean assumptions.

Q11Core.lean proves the complete insertion contract for arbitrary supplied
`Variable.AnchoredCore p d c`. Positive old entries increase by11, zero entries
remain zero, and size grows by11. The retained positive-positive sums increase
by22; the two removed sums1 and4 are filled by the proved replacement chains.
Both side permutations, all sums, endpoints H3/L(p+11-4), the legal anchor and
H4,L0,H0,L1 window persist. `q11_preserves_invariant` is universal, with no
finite upper bound on p or d. Its anchor displacement is10.

Q11Tracking.lean proves exact old-prefix lookup and maximum-pair preservation
for `ReverseComplement.TrackedCore`. The old pair must lie entirely before
L0. Its entries become p+11-1, its first index increases by len(P)=2, and it
remains before the new zero window. `source_step` therefore gives reflected
depth gain22-2=20; `source_iterate` gives size11a and depth20a after any a
steps. These are reflected depths, not the ordinary zero-window displacement.
Both reflected pair orientations are handled by the copied proved D6 symmetry
and oriented CorePair conversion.

## Finite recipe certificates and unbounded core induction

The six seed arrays and their tracked contracts are byte-identical copied D6
inputs. `exact_seed` identifies their exact reflected first depths
[26,26,26,26,24,27] at sizes16,...,21. A recipe contains nonnegative
(a,j,delta,padding), where a counts q11 moves, j counts q9 P2/P4 moves and
delta selects the seed. `recipe_coverage` proves a completed core at size

    p=16+delta+11a+9j+6 padding

for every depth in

    [b_delta+20a+14j, b_delta+20a+16j+1].

All insertions precede the final reverse-complement; C6 appends follow it.
The copied C6 theorem preserves the transformed zero positions. There is no
append-before-reflect assumption. The recipe theorem uses the complete q11,
q9, symmetry and append proofs and has no supplied graph-labeling hypothesis.

Q11Recipes.lean embeds all six starting rows p61..66 and all eleven bridge
rows p67..77 from the frozen author table. `base_finite_cover` and
`bridge_finite_cover` prove their entire bounded-depth coverage by kernel
`decide`, not native evaluation. The finite propositions evaluate every depth
in the stated band and require an actual recipe with exact size and depth
inequalities. `finite_cover_recipe` extracts a witness and `recipe_coverage`
then constructs the core. Thus these are kernel-checked finite recipe
certificates linked to a universal core proof; a Python table does not supply
an existence premise. `recipe-identities.json` compares all seventeen exact
rows with the frozen author verification table.

At p61..66, inherited D6 cores cover through105; the six finite recipes cover
106,...,F(p). This supplies cores throughout90,...,F(p). The eleven bridge
rows cover [F(p-6)+1,F(p)]. `F_shift` proves F(p+11t)=F(p)+20t for p>=61.
Every p>=67 has p=p0+11t with67<=p0<=77, so adding t q11 moves to the selected
finite recipe supplies the translated bridge at that exact size.

`growing_core_interval` uses strong induction on p. For depths through F(p-6),
it appends one C6 block to the earlier CORE. For higher depths, it uses the
translated bridge. It proves90,...,F(p) for every p>=61. The proof does not
append to arbitrary inherited full-spider labelings. `all_depth_core_coverage`
adds depths2,...,89 from the inherited D6 core theorem, whose bound is at least
105 at every p>=61. This proves the complete new core prefix unboundedly.

`coverage_spider` applies the freshly rebuilt generic odd shell k=2p+3 or even
shell k=2p+4 at p=floor((k-3)/2). The shell hypotheses require only the balanced
endpoints and extreme-offset positions, not a preserved insertion window.
The exact indexed graft identification, residual labeling, arm permutation and
whole-spider complement are copied proved D6 sources. The final graph theorem
discharges every core, residual, parity and identification premise.

## Nonregression, exact inverse and quantitative scope

`nonregression_finite` proves F(p)>=D6's core bound for all99 sizes p61..159
by kernel `decide`. Under p->p+99t, F increases180t and the old bound increases
176t. `F_dominates_D6` proves the unbounded comparison by exact division into
those99 residues. `prefix_dominates_D6` transfers it to all k>=19.
`F_monotone` and `prefix_monotone` prove nondecreasing behavior, including the
k124/125 seam.

The formal K7 is the inherited K6 for d<=89. For d>=90 it uses the equivalent
natural-arithmetic formula

    a=floor((d-104)/20), s=floor(((d-104) mod20)/4),
    K7(d)=125+22a+4s.

Natural subtraction is truncated at zero. Thus a=s=0 at d90..104 and the
remaining plateau cases implement the author's nonnegative ceiling formula.
`large_cutoff_spec` proves s<=4, D7(K7(d))>=d and D7(K7(d)-1)<d in the large
branch. `cutoff_covers`, `cutoff_previous_fails` and `cutoff_minimal` prove the
exact inverse relative to the sufficient displayed D7 function, for all d>=2
and k>=19. This is not a least graph-theoretic threshold.
`all_lengths_eventual_zero` supplies the same actual-spider conclusion for
every integer k>=K7(d), with all n,m and selected arms free.

`prefix_error_bound` proves for every integer k>=19

    11D7(k)<=10k,             10k-11D7(k)<=261.

The first inequality prevents natural subtraction from hiding negative error.
`prefix_ratio_precision_limit` proves the unbounded criterion

    forall precision:Nat, exists cutoff:Nat, forall k>=cutoff,
      precision * distance(11D7(k),10k) < k,

using cutoff=262*precision+19. The ordinary ratio interpretation gives an error
at most261/(11k) from10/11 through all integers. A literal Lean `Real` or
topological `Tendsto` theorem/equivalence is not included. The author's optional
maximal contiguous prefix within its restricted recipe union is also not
formalized here. Both limitations are separate explicit verification fields.

## Exact provenance, build, axioms and trust boundary

The frozen D6 source manifest is
`2f7d49ce7758a9834b212addd031ebd2d3bc2c16a8c03064afc44d4171f254f1`.
All45 copied proof modules are byte-identical. Its object files supply no final
imports. Exact q11 author report/manifest bindings are
`b6afd14b14d05344830fae350a0b170d6e6bfc1b2c341de57141d82d24465666` /
`00bde290bd400619849c1a907bf0ad9b10972c2256fe575a0cb6fb8c11fab0af`;
q11 mathematical audit bindings are
`f90b3ef57a1f9d9f762f99a2db7b68eef8d88c1862e35809794122e54be33a44` /
`720ef06b23bf2a7a5cc39dd02d260f519ac0939ad58e69be73f747ebe1ef4afd`.
Global D7 author report/manifest bindings are
`bf7eec616fa42a5465703e4f90d296f02dcb35a0b91c5c6c82bdfcf5208f9249` /
`419634baa520139e83395fb2014478710317d8bf72f83c4c7c54e31083be739d`;
global mathematical audit bindings are
`60a958449111a6f875be84a05d419c94c474db0cb770b3c07af799f57633c1cf` /
`4fd38e5e2b60ed6873105ffa751b5922a87a6a12f137956abf19e289f343c24a`.

Snapshots and complete original payload inventories are in inputs/,
input-bindings.json and frozen-inputs.json. Original identities are checked
before and after the build and by final verification. No original source,
author checker or solver was edited or executed.

The six new proof modules are Q11Gadget, Q11Core, Q11Tracking, Q11Recipes,
Q11Prefix and Q11Depth. The52nd source is Q11Audit. All52 modules rebuilt in the
previously absent build-final with `-DwarningAsError=true`, all exit codes zero.
Total compiler-call time is144,564 ms. Source hashes match before/after every
call. LEAN_PATH contains only this fresh object directory. Development objects
are retained as evidence and provide no final imports. The build protocol has
every command, source hash, exit code, timing and compiler output.

All658 named source theorems have explicit complete `#print axioms` outputs in
theorem-inventory.json and axiom-inventory.json. The sole union is `propext`,
`Classical.choice`, `Quot.sound`. No added mathematical axiom or sorryAx occurs.
The comment/string-aware lexical screen finds no sorry, admit, native_decide,
sorryAx, axiom declaration or unsafe declaration. Std is the sole external
source import. source-hashes.json records every compiled source.

Lean is4.34.0, Windows x86_64 release commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, compiler SHA-256
`a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`.
The Lean kernel/compiler and installed Std implementation remain trusted and
were not independently rebuilt or externally certified. Correctness is relative
to that toolchain, the explicit graph definitions and standard axioms. Python
identity and lexical checks are provenance/diagnostic gates, not proof premises.

## Immutable reproduction and boundaries

verify_final.py checks full build coverage, all658 axiom reports, exact sources,
inputs, toolchain, gadget and17 recipe rows. Its saved status is
`GO_FORMAL_D7_ALL_INTEGER_LENGTHS_PREFIX_EXACT_INVERSE_AND_INTEGER_RATIO`.
After freeze it compares saved records and all local manifest entries without
compiling or rewriting them. SHA256SUMS.txt binds all local payloads except
itself. For a fresh separate copied-source replay, copy this package elsewhere
and run `python -B build.py --build build-replay` there; compare sources and
axiom reports with the frozen inventories. Never compile or regenerate inside
this frozen package. Temporary generation scripts are not reproduction inputs.

D8 is outside this package. No public CMS/site/profile, published revision,
shared RESTART or cycle file was changed. Restricted recipe maximality,
remaining near-tip depths, unrestricted even depth one, unequal arm lengths,
new rooted-graft conclusions, global optimality and worldwide novelty are not
claimed by this formal artifact.
