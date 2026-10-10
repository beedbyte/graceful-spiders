# Private fixed-k95 full actual-vertex Lean theorem

10 October2026. **AUTHOR_KERNEL_GO; separate copied-source replay pending.** The complete fresh build and all author gates passed. This additive package is private. It changes no frozen predecessor, public copy, website, CMS or repository publication. Worldwide priority remains UNKNOWN; this internal AI-assisted construction/check is not external or peer review.

## Exact theorem

The proved principal kernel theorem is:

```lean
theorem GracefulBoundary.K95Full.all_vertices
    (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 95) :
    ∃ f : SpiderVertex n m 95 → Nat,
      Graceful (spiderGraph n m 95) (95*n+m) f ∧ f v=0
```

Thus the graph is the actual named `S(95^n,1^m)`, for every n>=2 and every m>=0. Each target receives its own labeling. The companion `unique_zero` strengthens the final condition to `∀ w, f w=0 ↔ w=v`. Neither theorem has a hidden path, source, H1, q24, D8, solver or finite-coverage premise. The only mathematical input hypotheses of the main statement are n>=2 and the supplied actual vertex. No full theorem for neighboring odd lengths follows.

## Exact finite coverage and its origins

The mathematical source report `graceful-k95-coverage-union-private-2026-10-10-a/report.md`, SHA256 `e613621a97f439c00672e69a2cf261885f0b463697bdeeaaa781999749a72d17`, is a provenance input, not a Lean axiom. Its manifest is `8766d164d0f66ec3795559f663310d3251a725a86fbc0c69aabdaadd48f4ea74`. This package constructs and checks the underlying source words directly.

|Actual target|Source used in this proof|
|---|---|
|Hub|Explicit root-zero residual labeling with odd radius47|
|Each existing short leaf|Complement of the residual labeling, with a proven leaf permutation|
|Arm depth1|Explicit near-center midpoint-alpha P191 word|
|Arm depths2..71|Frozen p46 compatible cores and the older H3 shell|
|Arm depths72/73|Frozen p19 delta3 seed; two old q9-fast insertions, one q9-slow insertion, complement reversal and H3 shell|
|Arm depths74..77|Frozen p37/q9 P4/P2 witness words; the depth77 overlap is retained|
|Arm depths78..86|Fixed t3 q24 B2/B4 words from the two frozen starting windows; the old family covers77..86|
|Arm depths87..92|All six independently checked frozen P191 literals, each retained as its own certificate|
|Arm depths93/94|Frozen H1 seed23, appended explicit C72, giving k95|
|Arm tip95|Direct endpoint-extension construction, including the true physical tip index94|

The interior catalog contains51 distinct literal words. `catalog.json` supplies an exact word, both extreme depths, chosen extreme, source origin and certificate number for every physical depth1..94. The six new source certificates respectively have (zero-depth,maximum-depth)=(86,87),(88,87),(88,89),(90,89),(90,91),(92,91). Whole-graph complement is used precisely for the maximum-derived cases. No source maximum is mistaken for a zero on the uncomplemented graph.

The D8 value at k95 is73 under the actual frozen D8 middle branch `25+16*((k-35)/18)`, where division is natural floor division. The older Compatible formula `27+14u+2 floor(u/2)` has value71 here and is not silently substituted for D8. The separate concrete72/73 source pair closes that exact distinction. These fixed literals establish the needed finite instantiation without importing an arithmetic bound as if it were a graph-existence theorem.

## Kernel certificate and actual graph transfer

Each literal theorem uses `FiniteAlpha.Certificate 46 z q path`, proved by kernel `decide` after unfolding that certificate and `GenericPathCertificate`. This checks the191 labels0..190, all190 edge differences1..190, alpha crossing cut94, the true midpoint index95 labeled94, and both prescribed extreme indices95-z and95-q. No native evaluation, opaque external certificate axiom or solver outcome is a proof premise.

The copied `FiniteAlpha.prescribed_zero` theorem then gives separate actual named-arm zero labelings for arbitrary n>=2,m>=0, using the previously proved residual/amalgamation and arm-permutation maps. The residual has the remaining n-2 full95-arms and every original short leaf. Its Q=95(n-2)+m edges receive weights1..Q; the alpha source weights shift to Q+1..95n+m. The graph is the literal `SpiderVertex`/`SpiderEdge` incidence structure. The hub is the physical source midpoint. Complement acts on the whole graph.

`K95Full.interior` performs the finite depth split1..94 and invokes that actual-graph theorem. `arm_depth_zero` translates physical depth d.val+1 to the exact `Fin95` index, then handles tip95 separately. `all_vertices` case-splits the actual vertex into hub, original leaf, or named arm position. When m=0 there is no `Fin0` leaf case to fabricate.

The new `K95Boundary` and `K95Tip` modules adapt the already frozen k71 constructions, with the exact substitutions71→95,70→94,69→93,35→47,36→48,37→49,34→46 recorded in `base-origins.json`. Their proofs are recompiled rather than assumed from numerical analogy.

## Fresh source build and trust boundary

There are35 modules:23 byte-identical predecessor sources through `FiniteAlphaTransfer`, two newly adapted boundary/tip modules, nine new literal-catalog modules and the new full wrapper. Every predecessor source is bound to the frozen k71 source index SHA256 `6bbf12e6b08470f42ccefd943ab936f20736975826f59bb5358a5f54dfa18b66` and copied anew; the earlier k71 copied-source replay report SHA256 `0dee5742778ce657e5972f7dc4986dec44870c0c037f48632a80b3befc173058` is additional provenance. No predecessor `.olean` is reused.

`build.py full` starts with an absent `objects-full` directory and compiles in source order from `source/`, passing bare module filenames and `-DwarningAsError=true`. `LEAN_PATH` contains only that run's newly built objects. Standard installed Lean/Std remains the external library/toolchain boundary. The compiler is Lean4.34.0, executable SHA256 `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`. This package does not independently rebuild or certify the compiler itself.

The earlier `dev` build verifies the initial dependency and boundary/tip work. Only the completed `full` build and subsequent explicit gates are final evidence; earlier development artifacts are retained and indexed separately. For source-only reproduction, copy `source/`, `module-order.json`, `build.py` and `checks.py` into a new directory without object/log output directories. Run `python build.py full`, then `python checks.py`. Each of the35 modules exited0 with warnings treated as errors. Final copied-source replay by another agent remains a separate gate after author freeze.

## Checks and limits

The solver-free Python graph checker validates51 words and1148 complete actual named graph labelings containing382,670 edges. Parameters are(n,m)=(2,0),(2,1),(3,2),(5,1), with every actual vertex separately targeted. Nine effective mutations reject a wrong midpoint, swapped extrema, target off-by-one, omitted/phantom leaf, wrong named arm, missing whole-graph complement, false tip94 and omitted leaf complement. Normal and optimized output bytes agree. These finite regressions supplement the kernel proofs and do not supply unbounded quantifiers.

The completed Lean gate inventories every theorem in all35 modules using the environment's actual module origins: **1678 theorem closures, all standard-only**. It rejects local added axioms and any closure beyond propext, Classical.choice and Quot.sound. Both principal theorem closures are exactly within this standard set. The gate checks every concrete vertex for n2m0,n2m1,n3m2: **671 named-vertex examples**, plus two symbolic theorem applications and three actual edge-incidence equalities. All passed.

Twelve effective Lean negative controls fail semantically, with all imports resolved and without recursion/heartbeat exhaustion: n=1 as an unsupported application premise, a phantom m0 leaf, false tip index95, wrong named arm, wrong physical target, missing original leaf in the edge count, root label1 substituted for0, false midpoint, false maximum, false low extreme, a certificate shifted from depth92 to93, and substituting arm length93. A rejected n=1 application is only a failure of this theorem's stated interface, not a proof that a path lacks a graceful labeling. Logs and generated control sources are retained under `checks/`.

Correctness status: author kernel GO for the exact theorem, with a separate copied-source replay still required after freeze. Source-level mathematical reports for all six new literals and the prior graph transfer are byte-pinned. Significance is the exact fixed-k95 full-vertex theorem with unbounded arm/leaf counts. Historical novelty is unassessed here and UNKNOWN. Older alpha, composition and path-labeling operations retain their prior attribution; newly catalogued literals and project coverage do not establish worldwide priority. No public release or external review is claimed.

The separately tasked aggregate mathematical catalog comparisons were still in progress when these author gates completed. No unfrozen aggregate report or mutable candidate is used as a proof premise. Their later reports and the separate Lean replay must bind this immutable packet additively. This author freeze does not pre-empt either independent gate.
