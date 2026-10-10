# Scoped k95 rooted-residual Lean author package

10 October 2026. Private additive formalization. **Author-side formal GO for the exact interior-arm theorem below; independent copied-source replay remains open.** No public release or priority claim.

## Exact theorem and scope

`GracefulBoundary.K95Rooted.interior` has hypotheses `H : IndexedGraph W F`, `root : W`, `g : W → Nat`, `Q d : Nat`, `ConventionalGraceful H Q g`, `g root = 0`, and `1 ≤ d ∧ d ≤ 94`. Its conclusion is the conjunction of `Q24Rooted.ZeroAt H root Q 46` at the two physical vertices `95-d` and `95+d` of the 190-edge source path. The center `95` is identified with `root`; these are depth-`d` vertices on the two newly attached 95-edge arms. `ZeroAt` asserts a conventional graceful labeling on the actual `graftGraph (pathGraph 190) H` with that named vertex labeled zero. The result holds for any finite residual indexed graph satisfying the supplied conventional graceful root-zero premise. It assumes neither a tree nor an alpha labeling nor surjectivity of the residual labeling.

The theorem gives separate labelings for each arm and interior depth. It makes no statement about depth 95, an old vertex of `H`, or obtaining root-zero at a prescribed residual vertex from an arbitrary graceful labeling. The onto conclusion would require an onto residual labeling; the non-onto triangle check below guards this distinction.

## Frozen evidence and source bridge

The mathematical transfer and its independent audit are pinned respectively to `research-audits/graceful-k95-rooted-residual-transfer-2026-10-10-a/report.md` SHA-256 `0704b6f204b44f294509c67c9be24c9e96ca5284806604b5049e4fb8b94c6e2d` and `research-audits/graceful-k95-rooted-residual-independent-2026-10-10-a/report.md` SHA-256 `6b9cf00a5d76ad86c2c38860e19a86879deffc2eadc55b46793c92b7ad0e962a`. The latter reports mathematical GO but explicitly discloses limited exposure to the author's prose; it is not an independent Lean replay.

The new `K95Rooted.lean` imports the frozen `K95Catalog8` module from the independently replayed fixed-k95 package; its source index SHA-256 is `e25a837ba4f27f6c7a1770e0f2ed245077f2eb282d6a8128c6d1b477c2a94d5d` and replay report SHA-256 is `9893d5686938f92df8638a2d36c9d00a53ecd1197714c50d14212b59ffc2fdfd`. It also imports a byte-identical copied `Q24Rooted.lean`, original source index SHA-256 `329f68dd57f383cf1bc420bfc7048cea06d9d70774ff9b55c3194e7152e086f6`. This existing generic module proves the actual graph amalgamation and residual transfer. The new source reduces the k95 case to its exact alpha path catalog, with no new axioms.

`packet_extreme` extracts the zero-or-maximum endpoint from a `GenericPathCertificate 46`. `catalog_extreme` discharges every `d=1,…,94` with 51 compiled finite path certificates. A separate literal checker verifies all 51 path label and weight inventories, midpoint/cut, 94 selected extremes, and three effective perturbations. The independent public catalog has 49 literally matching words and two alternate valid Lean words; all 51 pass the required contract. Finite catalog verification supplies exact premises, while the generic graft theorem supplies the unbounded residual-graph quantifiers.

## Fresh author build and controls

`checks.py` produced `results.json` with status PASS. It verified predecessor pins and Lean 4.34.0 executable SHA-256 `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`, then compiled the copied `Q24Rooted.lean` and new `K95Rooted.lean` into an empty temporary OLEAN directory using `-DwarningAsError=true`. Their reproduced object SHA-256 values are `973e6988650fac27ba8d948354a5edc33596a1a4c9e35d1e1006f9136cbb28aa` and `4eefc379d23bda54f5b57d1483da3ca9d971fdb481f4fb7fcae714e7cd1facc3`.

The exact principal theorem type was checked. The three new theorem axiom closures use only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms. The explicit non-tree, non-onto triangle instance passes for both new arms and all requested depths, while a strict onto claim fails. Four effective Lean mutants reject a nonzero chosen root, depth 95, an old residual vertex substituted for a new-arm target, and a false onto strengthening. These are interface controls, not graph nonexistence results. The new source and copied source contain no `sorry`, `admit`, `native_decide`, or new `axiom`.

This is an author build, even though the k95 catalog dependency came from a separate frozen replay and `Q24Rooted.lean` was compiled from a copied source. A separate reviewer must replay this exact new source and its pinned import closure before promoting formal status.
