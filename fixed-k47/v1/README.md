# Fixed 47-edge-arm zero-rotatability source package

**Beedbyte. Jordi Gartner publishes this work through Beedbyte.**

For every integer `n ≥ 2`, every integer `m ≥ 0`, and every actual named vertex `v` of `S(47^n,1^m)`, there is a graceful labeling `f` of that graph with `f(v)=0`. The labeling may depend on `v`. The vertices are exactly the center, all 47 depth vertices on each named arm, and the `m` original center leaves when present. This is the fixed arm length 47 theorem; it does not assert a theorem for every odd arm length or an unbounded q24/q30 family. The formal declarations are `GracefulBoundary.K47Full.all_vertices` and `all_vertices_unique_zero` in `source/K47Full.lean`.

The path boundary cases `n=2,m=0` (`P95`) and `n=2,m=1` (`P95` with one center leaf) have prior coverage. These overlaps do not determine priority for the full theorem. Worldwide priority is **UNKNOWN**. Internal checks are not external review or peer review.

## Notes and contents

This package includes the [English note](note.en.md), [German note](note.de.md), and [simplified Chinese note](note.zh.md). German and Chinese are draft translations without documented human language review. It also contains three content-only version notes, the exact 42 Lean source files, their topological build order and SHA-256 map, replay pins, a reproducible builder, and the full package checksum index. No PDF is supplied.

The independent copied-source replay used Lean 4.34.0 and freshly compiled all 42 modules with warnings treated as errors. It inventoried 2,201 theorem closures, including 111 private declarations; checked 191 actual named vertices for `n=2,m=0/1`; and rejected six semantic negative controls. The two principal theorem closures use only `propext`, `Classical.choice`, and `Quot.sound`. These are internal project checks, not external scholarly review or peer review. See `replay-pins.json` for the frozen report and source hashes.

## Reproduction

Use Python 3.9 or newer and Lean 4.34.0 with its installed standard libraries. Verify package bytes, source hashes, module order, and imports with:

```text
python build.py --check
```

Compile into a new directory outside this package:

```text
python build.py --lean /path/to/lean --output /path/to/new-build-directory
```

The builder checks the complete checksum index before compiling, sets `LEAN_PATH` only to the new output directory, removes `LEAN_SRC_PATH`, and compiles modules in order with `-DwarningAsError=true`. Logs and OLEAN files are written only to the requested output directory. No OLEAN file is included here.

## Earlier work and scope

Luiz, Campos, and Richter’s 2017 report covers the complete path cases `n=2,m=0` and `n=2,m=1`. Earlier root-zero, alpha-amalgamation, complement, and spider-gracefulness constructions are credited in the research notes. The bounded literature comparison does not establish that earlier work subsumes the full fixed-47 theorem. No novelty or worldwide-first claim is made.

The formal source establishes the named-vertex theorem for fixed `k=47`, all `n≥2,m≥0`. It is not a claim about all odd arm lengths. No reuse license is stated by this package.
