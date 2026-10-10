# q24 terminal arms over a rooted graceful residual: additive Lean author packet

Private author formalization, 10 October 2026. **Author formal GO for the scoped theorem below.** Separate copied-source replay and independent mathematical audit of this combined rooted-residual statement remain open. No public write or novelty claim.

## Principal result and graph

The new source `Q24Rooted.lean` proves `GracefulBoundary.Q24Rooted.terminal_four` for every `t≥1`, arbitrary indexed residual graph `H`, edge-label bound `Q`, conventional graceful labeling `g`, and specified root `r` satisfying `g r=0`. The actual graph in the theorem is exactly

`graftGraph (pathGraph (4*p+6)) H (center p) r`, with `p=22+12*(t−1)` and `center p : Fin (4*p+7)` at index `2*p+3`.

The path has `4*p+6=2K` edges and the root identification creates two **named** arms of length `K=2*p+3=23+24t`; all original residual vertices and edges remain. The theorem supplies separate conventional graceful labelings with zero at each of the four path vertices `K−d₀`, `K−d₁`, `K+d₀`, `K+d₁`, where `d₀=20+22t`, `d₁=21+22t`. The equalities relating the Lean `t−1` parameters to these exact `K,d₀,d₁` formulas are proved in `terminal_parameters`; they are not an informal index translation. The edge inventory of the actual graft is `1,…,Q+2K`, and every graph vertex has an injective label in `0,…,Q+2K`. The four existential witnesses may differ.

The hypothesis on `H` is only `Rooted71.ConventionalGraceful H Q g` and `g r=0`: **no alpha condition on `H` and no tree or onto-vertex condition** is inserted. A residual tree with a root-zero graceful labeling is included. The result does not put zero at an old residual vertex or at the new tips, and does not assert arbitrary-root zero-rotatability.

## Kernel proof route

`rooted_extreme` is a radius-parametric version of the frozen fixed-71 graft theorem. It derives path gracefulness and the path alpha cut from `GenericPathCertificate`, invokes the pre-existing kernel theorem `Rooted71.conventional_graft`, and complements the whole graft when the chosen path vertex initially has the maximum label. `reverse_certificate` proves the path certificate after reversal. `rooted_left` and `rooted_right` bind the graph's actual left/right path indices to selected depths. `terminal_four_s` instantiates these lemmas with the frozen q24 B1 `Q24Terminal.flip_certificate`; `terminal_four` gives the positive-`t` result.

The q24 path source gives midpoint cut label `K−1`, raw zero at left depth `d₀`, and raw maximum at left depth `d₁`. The graft labels the residual by `K−1+g`, preserves low path labels and shifts high path labels by `Q`. The path weights become `Q+1,…,Q+2K`; residual weights remain `1,…,Q`. No new `axiom`, `sorry`, `admit`, or `native_decide` appears in the new theorem source.

## Compilation and controls

`checks.py` verifies predecessor source-index pins and the Lean executable hash, then compiles `Q24Rooted.lean` with `-DwarningAsError=true` to a **new temporary OLEAN directory**; it imports pinned predecessor objects and uses no author object for this new module. The resulting OLEAN SHA-256 is `641ae2040d5d1d5b581747541461b5228b14564d9aef214082fc117dec886d12`. Seven named theorem axiom closures are exactly `[propext, Classical.choice, Quot.sound]`. `TriangleCase.lean` instantiates the complete four-target `t=1` theorem for the three-edge cycle with labels `[0,1,3]`; its strict onto-vertex version is separately disproved by the frozen `triangle_not_onto` theorem. This checks a genuine non-tree, non-onto residual and the actual graph constructor.

Three semantic mutations fail under the same fresh object: wrong specified root (`g r≠0`), falsely upgrading the triangle to the stronger onto `Graceful`, and using an unsupported depth. Their failures are compile errors at the intended hypotheses/types, recorded in `results.json`. The prior independent finite mathematical checker also tested the literal graph incidences and high-side shift/complement mutations, but this Lean packet does not promote those finite executions into proof.

## Frozen input pins and status boundary

- q24 B1 Lean author report SHA-256 `5938f32ddc195cf59ef3f98074adf906c3b49d534937203277af2fc37b933bd1`; `Q24Terminal.lean` SHA-256 `088fd226e1c2adb57556ebd1fc047ba8494546511cb8096d4d089f679aefcc91`; complete source index SHA-256 `c55f3f4af89434b2ab9439d5391237834b4f767a81a19daab3b26123a47db66d`.
- Rooted-residual Lean report SHA-256 `c142a9e8d20c490b1e8017877f78e4d7045413421e960d4f377cc6263427e385`; `RootedInjective.lean` SHA-256 `688e8761808978138bf749497295928d13a3e7903bdd21f95ab2c78f22d5f186`; `RootedTriangle.lean` SHA-256 `9ede496084620bdeadc3736a44c7c58656a30a4fd45fd9cef211894234029ad6`; complete source index SHA-256 `45b2c193ce997f0d150dd90be66c13dff6daf38f666671dd887d177d3d775eba`.
- Prior scoped mathematical audit report SHA-256 `f0fd75067fa68c66c39a6d445e520776fdf0807abca0189e5f1ae6f491454166`, manifest SHA-256 `4d7973a66ecb5b9c5b50f4e483ee76afa279fe3d1370ca966adc8055c96704f0`. This is supporting author evidence, **not** a separate replay or independent review of the present source.

No predecessor files were changed. `manifest.json` binds the additive source, checks, mutations, results, and report. Formal release status remains **HOLD** pending a separate copied-source build and independent mathematical comparison of the exact theorem interface.
