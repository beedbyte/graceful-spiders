# Fixed 23-edge arms: Lean source package

**Beedbyte. Jordi Gartner publishes this work through Beedbyte.**

This package contains 27 Lean source modules for the fixed-length statement: for every `n ≥ 2`, `m ≥ 0`, and each actual named vertex of `S(23^n,1^m)`, there is a graceful labeling assigning zero to that vertex. The labeling may depend on the selected vertex. The endpoint is `GracefulBoundary.K23Full.all_vertices` in `source/K23Full.lean`; its companion theorem makes every other vertex positive. This is a result for **arm length 23 only**.

Read the short [English](note.en.md), [German](note.de.md) and [simplified Chinese](note.zh.md) research notes. German and Chinese are draft translations without documented human language review. The three [version notes](version-note.en.md) are also supplied in [German](version-note.de.md) and [Chinese](version-note.zh.md).

## Reproduce the source build

The package includes exactly 27 byte-pinned `.lean` files, a topological `build-order.json`, a `source-sha256.json` map, and a complete `SHA256SUMS.txt`. The build requires Lean 4.34.0 with its installed standard libraries and Python 3.9 or newer. Verify bytes and imports with `python build.py --check`. To compile, choose a directory that does not exist yet, outside this package:

```text
python build.py --lean /path/to/lean --output /path/to/new-build-directory
```

The script sets `LEAN_PATH` only to the new directory, removes `LEAN_SRC_PATH`, compiles from `source/` using bare module filenames, and treats warnings as errors. The author's source build and a separate internal copied-source replay both succeeded. The replay freshly compiled all 27 modules with warnings as errors, audited 1,649 theorem closures against the standard Lean axioms, and rejected five semantic negative controls. The source files, rather than compiled objects, are distributed here. No PDF is included or claimed.

## Scientific and publication limits

The older path results already cover the `n=2,m=0` path and the `n=2,m=1` central-leaf path. The source proof uses the established midpoint-alpha amalgamation and literal 47-vertex path certificates for positions absent from the earlier bounded project inventory. Those operations and older overlaps are credited in the notes. The full Cattell path-construction comparison has not been completed; worldwide priority of the all-`n,m`, all-vertex fixed-23 statement is unknown. Internal project checks are not external scholarly review.

AI tools assisted construction and proof development, coding, Lean formalization, certificate checking and source comparison for this work. No reuse license is granted by this package; rights are reserved. Publication and external review are separate decisions.
