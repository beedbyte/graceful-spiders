# A widening zero-label interval: Lean source package

**Beedbyte. Jordi Gartner publishes this work through Beedbyte.**

For every integer `t ≥ 0`, set `k = 23 + 24t`. For all `n ≥ 2`, `m ≥ 0`, each named long arm of the actual `S(k^n,1^m)`, and every depth `17 + 20t ≤ d ≤ 20 + 22t`, a graceful labeling can place zero at that arm's actual depth-`d` vertex. The labeling may depend on the named arm and depth. The formal endpoint is `GracefulBoundary.Q24Seed5Mix.combined_interval_actual` in `source/Q24Seed5Mix.lean`. At `k=47` the interval is `37..42`; at `k=71` it is `57..64`. This package does not prove every vertex at those lengths or all odd lengths.

Read the [English note](note.en.md), [German draft translation](note.de.md), and [simplified Chinese draft translation](note.zh.md). The three content-only [version notes](version-note.en.md) are also supplied in [German](version-note.de.md) and [Chinese](version-note.zh.md). The English original has internal editorial and mathematical checks; human language review of the translations is not documented.

## Reproduce the source build

The package includes exactly 33 byte-pinned `.lean` source files, a topological `build-order.json`, `source-sha256.json`, and a complete `SHA256SUMS.txt`. It requires Lean 4.34.0 with its installed standard libraries and Python 3.9 or newer. Verify all package bytes and imports with `python build.py --check`. To compile, choose a directory that does not exist yet, outside this package:

```text
python build.py --lean /path/to/lean --output /path/to/new-build-directory
```

The script sets `LEAN_PATH` only to that fresh directory, removes `LEAN_SRC_PATH`, compiles from `source/` using bare module filenames, and treats warnings as errors. The frozen author build and a separate internal copied-source replay both compiled all 33 modules; the latter checked 1,862 theorem closures against standard Lean axioms and rejected eight semantic negative controls. Only source files are distributed, not compiled objects. No PDF is included or claimed.

## Scope and publication limits

At `t=0`, this interval is part of the previously established [fixed-k23 result](../../fixed-k23/v1/README.md). For every `t`, earlier path results already cover the `n=2,m=0` and central-leaf `n=2,m=1` subfamilies. This construction uses established alpha-amalgamation. Its whole interval does not remain above the older D8 sufficient prefix, although an unboundedly growing portion does. The full Cattell path construction and composed older operations have not been classified for this joint source interface; worldwide priority is unknown. Internal project checks are not external scholarly review.

AI tools assisted development of the mixed B2/B4 construction, coding, source comparison and Lean formalization. No reuse license is granted by this source package; rights are reserved. Publication and external review are separate decisions.
