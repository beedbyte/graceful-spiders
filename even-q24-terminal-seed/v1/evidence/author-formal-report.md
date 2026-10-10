# Parameterized terminal-12 even-seed formalization

10 October 2026. Private additive formal packet. **GO for the exact formal theorem below.** All84 modules compiled afresh, the nine principal axiom closures passed, and all ten semantic controls failed because their altered propositions were false. This packet is an internal Lean development and local copied-source build; it is not external review, a publication or a historical priority claim. Predecessor source bytes are preserved.

## Exact formal theorem

`GracefulBoundary.EvenSeedFamily.Seed K0 z0 seed` is the frozen K26 development's general even `State K0 z0 seed`, strengthened by `3≤z0`. Expanding that structure gives exactly K0≥26, even K0, odd z0, z0+2<K0, length2K0+1, even tags0,…,K0, odd tags0,…,K0−1, sums0,…,2K0−1, physical midpoint tagK0, local tags1,0,0,2 at indicesz0−1,…,z0+2 and terminal12. The state also states the redundant condition1≤z0. There is no fixed K0 or seed literal in the universal theorem.

`EvenSeedFamily.all_states` proves, by structural induction on an arbitrary list of B2/B4 choices, the state

`Seed (K0+24*bs.length) (z0+2*bs.length+2*bs.count true) (word z0 seed bs)`.

This parameterizes the initial word and zero position. Each induction branch uses the frozen K26 module's already general even-state `q24_preserves_B2` or `q24_preserves_B4`. It does not instantiate its fixed K26 history theorem or extrapolate finite computations. The predecessor's complete side, sum, midpoint, terminal and local-window invariants are inherited through these kernel-checked promotion theorems.

`EvenSeedFamily.window_arithmetic` proves that every integer depth in

**[K0−z0−1+20t, K0−z0+22t]**

has the required source index for some number j≤t of B4 steps. The proof divides the distance from the upper endpoint by2 and handles the remainder0 or1. Mixed histories supply the corresponding state. The frozen general `state_root_path_certificate` decodes that state into a complete midpoint-alpha path, with maximum2K at indexz and zero at indexz+1. This source interface holds for every seed, independently of either new literal.

`EvenSeedFamily.rooted_window` has arbitrary indexed graph H, specified root, supplied `Rooted71.ConventionalGraceful H Q g` and g(root)=0 as premises. For K=K0+24t and the interval above it concludes:

`EvenRootedPrefix.ZeroAt H root Q K ⟨K−d,…⟩ ∧`

`EvenRootedPrefix.ZeroAt H root Q K ⟨K+d,…⟩`.

These are the actual two named new arm vertices on the graph formed by identifying the path midpoint with the supplied root while retaining every H vertex and edge. Each ZeroAt contains a separate conventional graceful labeling and a proof that the selected actual vertex is zero. The theorem invokes the generic conventional root-zero graft through `rooted_left` and `rooted_right`; path reversal chooses the opposite named arm and whole-graph complement handles a maximum target. H has no tree, connectedness, vertex-onto or alpha premise. The supplied conventional graceful labeling remains an assumption, rather than a claim that every graph has one.

## Literal K30 and K28 instances

`K30Seed.lean` defines the exact61-entry K30 literal from the frozen mathematical packet and the exact57-entry K28 literal. `seed30_valid` proves `Seed 30 3 seed30`; `seed28_valid` proves `Seed 28 9 seed28`. Both proofs discharge every finite state field using ordinary kernel-checked `decide`; no search solver, Python checker, `native_decide` or runtime result is a proof premise.

`k30_window` specializes the universal graph theorem to **K=30+24t and d∈[26+20t,27+22t]**. `k28_window` similarly gives **K=28+24t and d∈[18+20t,19+22t]**. Both are all-t theorems on both named arms, for arbitrary supplied conventional graceful root-zero H.

## K30 D8 join

The copied all-even rooted-prefix source's `all_even_prefix` supplies depths2,…,D8(K) for this same arbitrary-H graph and both named arms. Its interface is used directly; the actual-spider theorem in GapDepth alone is not substituted for an arbitrary-H result.

`k30_D8_identity` proves, for every t≥4,

`D8(30+24t)=30+24t−19−2*((12t−48)/11)`.

Division is natural-number division and 12t−48 is nonnegative under this hypothesis. `k30_seam_gain` proves both **26+20t≤D8(30+24t)+1** and **D8(30+24t)<27+22t**. `k30_exact_seam` proves the seam inequality holds **if and only if t≥4**, using the formula above for the infinite branch and the four exact earlier branch evaluations. Thus this is an exact threshold proof, not a finite test followed by extrapolation.

`k30_joined_prefix` splits on d≤D8(K), applies the old arbitrary-H prefix theorem on that branch, and applies the new universal seed window otherwise. It proves **2≤d≤27+22t for every t≥4**, separately on both named arms of the same grafted graph.

The earlier interval gaps remain12–25 at t0,42–45 at t1,58–65 at t2 and74–85 at t3. The exact seam theorem says these two listed guarantees fail to join there; it does not prove graph nonexistence at any omitted depth.

## Reproduction and integrity

`predecessor-pins.json` identifies every exact original ancestor source and SHA256. Eighty-two ancestor modules were byte-copied from the frozen K26 formal package and the published/staged all-even rooted-prefix v1 source package. Overlapping module names were required to have identical bytes before copying. The two new proof modules are `EvenSeedFamily.lean` and `K30Seed.lean`; all84 modules are ordered in `module-order.json`.

`build.py` uses the existing Lean4.34.0 executable pinned to SHA256 `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`. It compiles the copied source into an initially empty local object directory with warning-as-error and that directory alone on LEAN_PATH. It then compiles `checks/Audit.lean`, prints the exact principal theorem heads and nine axiom closures, and runs the semantic failure controls. The result file and logs preserve every exit code and axiom inventory. A successful run is required for GO in the manifest.

From this private directory run `python -B build.py objects-reproduce` using an unused output directory name. The package needs no download or external write. Logs go to the corresponding `objects-reproduce-logs` directory. The script checks original source pins and copied source equality before compiling, and rechecks predecessor pins after the run.

The positive audit formally supplies a cyclic nononto triangle labeled0,1,3, and that triangle with an isolated vertex labeled2. It typechecks the actual named K30 targets at t0,d26 and the joined-prefix boundary at t4,d115 over the disconnected graph. These examples check graph semantics; the all-H proof itself remains parametric.

Ten controls assert false source contracts: wrong alpha cut, false triangle onto claim, wrong midpoint, a depth outside the seed window, nonzero supplied root, false seam at t3, shifted zero window, wrong terminal, unreversed opposite-arm source index, and zero asserted at the source maximum index. Each must fail with a genuine Lean error. They establish rejection of those altered contracts, not nonexistence of other graceful labelings.

The source scan found only two comment occurrences of the word `axiom` in a preserved predecessor Interfaces.lean; there are no `sorry`, `admit`, `native_decide`, unsafe declarations or added axiom declarations in the proof source. The checked axiom closures are constrained to the standard set `propext`, `Classical.choice`, `Quot.sound`, with the exact subset for each theorem retained in the build result. Hash inventories and the private manifest seal the final package and confirm predecessor bytes remain unchanged.

## Limits

The exact formal scope is the universal seed window, the two literal instances, and the K30 D8 identity, exact join threshold and joined arbitrary-H prefix. This packet does not formalize the more general all-seed D8 threshold/asymptotic formulas or the endpoint-sum/K24 obstruction from the mathematical report. Those remain the separately checked mathematical statements in the earlier audit.

The theorem is conditional on a seed; no seed existence at every even K0, K0→K0+2 promotion, all residue classes, every depth, old H vertex coverage, simultaneous zeros or open-conjecture resolution is claimed. Existing actual-spider constructions may overlap these vertices. Generic alpha graft and the B2/B4 gadgets are reused predecessor results. Historical/worldwide priority and exhaustive non-subsumption remain **UNKNOWN**. No new literature search or public, CMS, profile or GitHub write was performed. A separate copied-source review of this new formal packet remains a later gate coordinated with the root chat.
