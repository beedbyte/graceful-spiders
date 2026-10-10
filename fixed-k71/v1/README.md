# Fixed 71-edge-arm zero-rotatability source package

**Beedbyte. Jordi Gartner publishes this work through Beedbyte.**

For every `n ≥ 2`, every `m ≥ 0`, and every actual named vertex `v` of `S(71^n,1^m)`, there is a graceful labeling with `f(v)=0`. The labeling may depend on the selected vertex. Vertices include the hub, all 71 named depth vertices on every arm, and all `m` original center leaves when present. This is fixed `k=71` only; no all-odd-length theorem is claimed. The formal declarations are `GracefulBoundary.K71Full.all_vertices` and `all_vertices_unique_zero` in `source/K71Full.lean`.

The path cases `n=2,m=0/1` have prior coverage. Worldwide priority is **UNKNOWN**. There is no novelty, external-review, or peer-review claim.

## Package contents

The package has the 45 exact Lean modules in the frozen author source set, build order, SHA-256 source map, reproducible builder, replay pins, English note, draft German and simplified Chinese notes, and content-only version notes. No PDF is supplied. German and Chinese are draft translations; human language review is not documented. The independent copied-source replay is complete: all 45 modules were rebuilt from byte-identical copied sources with warnings as errors and no author OLEAN imports. The principal theorem has only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`; the replay audited 2,048 theorem closures, compiled 503 named-target instances, and rejected 12 effective mutations. Replay report SHA-256: `0dee5742778ce657e5972f7dc4986dec44870c0c037f48632a80b3befc173058`. This is an internal reproducibility check, not external scholarly review.

## Reproduction

With Python 3.9+ and Lean 4.34.0, verify all package hashes, inventory, imports and order with `python build.py --check`. Compile outside the package with `python build.py --lean /path/to/lean --output /path/to/new-build-directory`. The builder sets `LEAN_PATH` only to the new output directory, removes `LEAN_SRC_PATH`, and uses `-DwarningAsError=true`. No OLEAN files are included.

## Earlier coverage and scope limits

Luiz, Campos, and Richter (2017) cover the path cases `n=2,m=0/1`. See the pinned primary-scope record for related constructions and limitations. Internal checks are not external scholarly review. No q-family or all-odd theorem is claimed.
