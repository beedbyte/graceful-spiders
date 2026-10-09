# D8 separate internal copied-source Lean replay

9 October 2026. **GO for the scoped all-integer actual-spider D8 prefix,
universal q10 construction/tracking, seven recipes, unbounded q11 translation,
D8≥D7, monotonicity, deficit bounds and integer ratio criterion.** No blocking
discrepancy was found. K8 inverse/minimality is outside this audit and package.
This is an AI-assisted internal project check, not external review or scholarly
peer review. Assistance here covered identity checks, source inspection,
compiler replay, inventory comparison and negative controls. Jordi Gartner
publishes the work through Beedbyte. No public content or shared checkpoint was
changed.

## Frozen identity and isolated build

Author package: `../graceful-q10-gap-fill-formal-2026-10-09-a`.
Manifest SHA256:
`a5aaf2d94b7eb81198f7a16e8e84b30cf21bf9e40259075ec94d195183d83619`.
Report SHA256:
`2b64ceb508e9fa60bb8094c1f0689bea7c63f2d8d56dba9d82d0aaf03286d2da`.
All 315 payload entries and complete author manifest coverage were checked
before and after replay. Copied source/input identities and all bound original
predecessor manifests/payloads also verify. No original source, input or record
was changed, and no author-package build/checker script was executed.

All formal sources and binding inputs were copied here. Author build directories
were excluded. All 57 modules pass a fresh `-DwarningAsError=true` build in the
previously absent `build-replay`, whose isolated `LEAN_PATH` includes only fresh
local objects. Author objects supply no local import. Source hashes were checked
around each call. Logs, commands, source hashes, timings and toolchain identity
are preserved. Copied author `report.md`, `README.md`, `verification.json` and
inventories retain their original author meanings; this report and
`replay-verification.json` record the separate check. Original manifest bytes
are retained in `AUTHOR-SHA256SUMS.txt`.

## Exact graph scope and quantitative conclusions

Inspected `GapDepth.lean`, `GapRecipes.lean`, q10 core/tracking/gadget sources
and fresh principal theorem output. The principal declaration is:

```lean
theorem all_lengths_prefix_zero (k n m d : Nat) (hk : 19≤k)
    (hn : 2≤n) (a : Fin n) (hd : 2≤d ∧ d≤depthPrefix k) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0
```

Namespace: `GracefulBoundary.GapFill`. D8 equals D7 through k124. At k≥125,
p=floor((k-3)/2), a=floor((p-61)/11), r=(p-61) mod11 and
D8(k)=107+20a+2r. Every natural k≥19, n≥2, m≥0, selected arm and depth
2≤d≤D8(k) is quantified, including both parities and n=2,m=0. There is no
finite upper bound. Different requested vertices may use different labelings.

The byte-identical inherited `SpiderVertex`/`spiderGraph` contract is the actual
center, n arms of k vertices and m short leaves, with the corresponding center,
successive-arm and leaf edges. `Graceful` requires full vertex-label bijections
onto 0..n*k+m and actual absolute edge differences onto 1..n*k+m. Odd/even
transfer premises are discharged by the proof; no supplied core, parity,
residual-gracefulness or identification assumption remains. `prefix_inside`
proves D8(k)<k and the principal theorem returns the legal index bound.

`prefix_dominates_D7` proves D8≥D7 pointwise. `prefix_monotone` includes the
k124/125 seam; at the high-branch residue rollover, the prefix can remain
constant. For k≥125, `tail_error_bound` proves
11D8(k)≤10k and 53≤10k-11D8(k)≤83. For every k≥19, `prefix_error_bound`
proves 11D8(k)≤10k and 10k-11D8(k)≤261. The nonnegative inequality prevents
natural subtraction from masking an error of the opposite sign. The unbounded
integer precision criterion uses cutoff 262*precision+19. A literal real
Tendsto theorem/equivalence, K8 inverse and recipe-family maximality are absent.

## q10 and recipe construction

The exact q10 gadget is P=[3,8], B=[10,8,9,10,5,5,4,2,3,4],
D=[1,1,2,6,6,7,7,9]. Kernel `decide` checks the chain/side certificate.
`q10_preserves_invariant` universally preserves the full anchored core,
increases size by10 and low-zero anchor depth by12. Maximum-pair tracking
increases its index by2, hence reflected first-depth gain18.
`source_iterate` proves size10b/depth18b for every iteration count b.

Recipes use the two exact tracked seeds of sizes16,17 and reflected start26.
The universal recipe theorem performs q9, q10 and q11 insertions in that order,
then one final reflection. A recipe gives size16+delta+9c+10b+11a and depths
26+16c+18b+20a and its neighbor. The seven exact literals cover added depths
at p62,64,66,68,70,71, with two pairs at p71. `finite_gap_cover` checks all
eleven base residue cases p61..71 by kernel `decide`, including empty gaps.

For any p≥61, exact division selects p0∈61..71 and p=p0+11t. Adding t q11
moves before reflection shifts both endpoints by20t and size by11t. This is
the unbounded translation, not a finite extrapolation. `all_depth_core_coverage`
combines inherited D7 core coverage with the new gaps at the same target size.
The copied generic spider transfer then gives the final graph statement.

The new audit checker independently compares gadget P/B/D, all seven recipe
counts/order/depths and both seed literals with the bound author JSON inputs.
Every exact comparison passes. Search statuses and Python calculations do not
supply Lean proof premises.

## Inventory and negative controls

The separate checker reconstructs namespace-qualified theorem names and parses
fresh compiler axiom output. All 706 names and all 706 explicit axiom reports
match the frozen inventory, with each report occurring exactly once. The sole
dependency union is `propext`, `Classical.choice`, `Quot.sound`; principal lists
are preserved individually. No nonstandard mathematical axiom or `sorryAx`
appears. The comment/string-aware lexical screen finds no `sorry`, `admit`,
`native_decide`, `sorryAx`, `axiom` or `unsafe` code token. All 57 root sources
are covered, and `Std` is the sole external import. The query module is freshly
rebuilt from these objects.

Two separate focused mutations are rejected by the same compiler and ordinary
`decide`: changing q10 P's first value3→4 breaks its chain/boundary certificate;
removing the p71 lower pair recipe leaves only depths126,127 and breaks complete
gap coverage. Later theorem users are excluded so the tested rejection is an
actual false certificate, not a downstream type or import failure. Compiler
logs and commands are in `negative-controls/`.

A separate GapDepth copy with one appended newline is rejected by the recorded
source-identity equality gate. Expected/mutated hashes and the rejection are
saved. Positive sources and author bytes remain unchanged.

## Trust and freeze

The toolchain is Lean4.34.0 Windows release commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, compiler SHA256
`a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`.
The kernel/compiler and installed Std remain trusted and were not independently
rebuilt or externally certified. This check confirms replay and scope relative
to those components and standard axioms. It establishes neither external peer
review nor historical priority, global optimality, full zero-rotatability,
near-tip completeness, unequal-arm results or unrestricted even depth one.

The new local manifest binds every payload except itself. Check frozen bytes
read-only with `python -B freeze_audit.py --verify`. Reproduce in another fresh
copy rather than recompiling or regenerating inside this frozen record.
