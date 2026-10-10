# q24 arbitrary rooted residual: independent copied-source Lean replay

**Private scoped GO, 10 October 2026.** This is an independent Lean 4.34.0 replay of the frozen author theorem `GracefulBoundary.Q24Rooted.terminal_four`, not an external review, worldwide priority finding, or public release. The author report SHA-256 is `7fe5063608bdb1ebf32ce5574ea52e7d956cf6ddccc55e073ce92490b648e5b0`; its source index SHA-256 is `329f68dd57f383cf1bc420bfc7048cea06d9d70774ff9b55c3194e7152e086f6`; the exact `Q24Rooted.lean` source SHA-256 is `3920203716673dac6a87393e48043a78a94fc8e9fa1389eb66e3e4dee4f76024`.

## Independent build and theorem interface

I checked the frozen source indices for the q24 predecessor (SHA-256 `c55f3f4af89434b2ab9439d5391237834b4f767a81a19daab3b26123a47db66d`) and rooted-residual predecessor (SHA-256 `45b2c193ce997f0d150dd90be66c13dff6daf38f666671dd887d177d3d775eba`). They contain 34 and 58 modules; their 33 overlapping source names have identical bytes. Adding `Q24Rooted.lean` gives **60 distinct exact sources**. My `replay.py` copied all 60 to a new tree, derived a topological order from their literal imports, and compiled them to an initially empty separate OLEAN directory. It did not load or copy any author OLEAN or run an author build script. All 60 modules passed `-DwarningAsError=true`, yielding 60 fresh OLEANs. Lean identifies as version `4.34.0`, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`; executable SHA-256 `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`. The independently produced principal OLEAN SHA-256 is `f6bfcdca5670134fbe88c6a2a796dca3eae354c43fc2d34dd2962ef05dbde52f`.

The kernel query prints the exact type: for arbitrary indexed graph `H : IndexedGraph W F`, arbitrary `Q`, conventional graceful `g : W → Nat` with `g root=0`, and all `t>=1`, it yields a conjunction of four `ZeroAt` propositions. Each `ZeroAt` existentially supplies its **own** injective vertex labeling into `0..Q+2K` and complete edge weights `1..Q+2K` of the actual graft

`graftGraph (pathGraph (4*p+6)) H (center p) root`, `p=22+12*(t−1)`, `K=2*p+3=23+24t`, `center p=K`.

The four named path vertices are `K−d₀`, `K−d₁`, `K+d₀`, `K+d₁`, with `d₀=20+22t`, `d₁=21+22t`. At `t=1`, the query compiles the non-tree triangle residual for path indices `5,4,89,90` in `Fin 95`: these are the two depths on each of the two named 47-edge arms. The path has 94 edges, the triangle has `Q=3` edges, and the graft edge bound is 97. No alpha condition, tree hypothesis, or onto-vertex hypothesis is imposed on `H`; `ConventionalGraceful` means vertex injectivity into the allowed interval and a bijection of edge weights. The triangle's labels `[0,1,3]` omit vertex label 2, and `triangle_not_onto` proves it is not `Graceful` in the stronger onto-vertex sense. This independently exercises the precise conventional scope and actual graft constructor.

The seven new declaration closures (`reverse_certificate`, `rooted_extreme`, `rooted_left`, `rooted_right`, `terminal_parameters`, `terminal_four_s`, `terminal_four`) each report exactly `[propext, Classical.choice, Quot.sound]`. The triangle conventional instance reports a subset of these standard axioms; its not-onto theorem reports none. The printed theorem type and the compiled four-target triangle instance bind the interpretation above to the fresh objects.

## Negative controls and limits

My three separate Lean mutants all failed under the same fresh objects, for the intended reasons: choosing the triangle vertex labeled 1 as root cannot satisfy `g root=0`; upgrading its conventional graceful witness to strict onto `Graceful` is a type mismatch; and using the first terminal projection to claim a midpoint zero is a target-index mismatch. The mutants test the theorem interface, not global impossibility of a midpoint-zero labeling by some other method.

**GO scope:** exact copied-source compilation, theorem-type/axiom query, conventional non-onto triangle instance, and the three semantic guards. **Remaining limit:** this replay does not independently reprove the large pinned predecessor modules by a second mathematical argument, establish novelty, place zero at a residual vertex or tip, or imply arbitrary-root zero-rotatability. No public write occurred.

## Frozen replay pins

- Copied-source index SHA-256: `3cbe8a148c44d9e65770646f4465be1cbe2518bf5e4c60941ce0cd35f355f103`.
- Fresh-object index SHA-256: `8e35db0c5a2cbbf15552e0c1be68a3076503461fa5756330258f332e01f485cd`.
- `build-result.json` SHA-256: `6005e3c72e0fe452023c8abc3a17e74b28726289c90c2a67639ccaf1e956743f`.
- `control-result.json` SHA-256: `0f6f829f07c58bdd0795dc87a067a6836317005967b2568826ad22aea65f4e3d`.
