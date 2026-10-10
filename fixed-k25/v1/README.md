# Fixed 25-edge arms: Lean source package

**Beedbyte. Jordi Gartner publishes this work through Beedbyte.**

For every `n ≥ 2` and `m ≥ 0`, each actual vertex of `S(25^n,1^m)`—the center, every named vertex on each 25-edge arm, and every original center leaf—can be labeled 0 in a graceful labeling. The labeling may depend on the chosen vertex. The exact declarations are `GracefulBoundary.K25Full.all_vertices` and `all_vertices_unique_zero` in `source/K25Full.lean`. The unique-zero companion additionally makes every other vertex label positive. This package proves the fixed length 25 only; it does not state an all-odd or unbounded F20/F18 Lean theorem.

The `n=2,m=0` graph is the path `P51`, whose vertices were already covered by the path 0-rotatability result. For `n=2,m=1`, the graph is `P51` with one leaf at its central vertex; this case is covered by Theorem 14 of Luiz, Campos and Richter, [“Some families of 0-rotatable graceful caterpillars” (2017)](https://ic.unicamp.br/~reltech/2017/17-12.pdf). These overlaps do not settle priority for the full all-`n,m` fixed-25 statement. Worldwide priority is **UNKNOWN**.

## Contents and reproduction

This version contains exactly 27 byte-pinned Lean source modules, their topological `build-order.json`, a `source-sha256.json` map, [English](note.en.md), [German](note.de.md), and [simplified Chinese](note.zh.md) research notes, three content-only version notes (`version-note.en.md`, `version-note.de.md`, and `version-note.zh.md`), a reproducible `build.py`, and a complete `SHA256SUMS.txt` index. The German and simplified Chinese notes are draft translations without documented human language review. `editorial-copy-pin.json` identifies the frozen trilingual copy used for these notes. No PDF is supplied.

Use Python 3.9 or newer and Lean 4.34.0 with its installed standard libraries. Check package bytes and imports with:

```text
python build.py --check
```

Compile into a new directory outside this package:

```text
python build.py --lean /path/to/lean --output /path/to/new-build-directory
```

The script verifies the checksum index, module order, imports, and source hashes before compilation. It sets `LEAN_PATH` only to the new output directory, removes `LEAN_SRC_PATH`, compiles from `source/` in module order with warnings treated as errors, and writes the module logs and output hashes outside the package. The package includes source files, not compiled OLEAN files.

A separate internal copied-source replay recompiled all 27 modules, inventoried 1,649 theorem closures (103 private), checked 103 named `n=2,m=0/1` instances, and rejected five semantic negative controls. Both principal theorem closures use only `propext`, `Classical.choice`, and `Quot.sound`; no package-local axiom was found. The replay pins are in `replay-pins.json`. These are internal project checks, not external scholarly or peer review.

AI tools assisted construction and proof development, coding, Lean formalization, certificate checking, and source comparison for this work. No reuse license is stated by this package.
