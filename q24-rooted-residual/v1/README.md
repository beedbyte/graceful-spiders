# Prescribed zero labels on two arms grafted to a graceful rooted graph

**Beedbyte — source package v1.** Jordi Gartner publishes this work through Beedbyte.

## Exact theorem

For any integer `t ≥ 1`, put `K = 23 + 24t`, `d₀ = 20 + 22t`, and `d₁ = 21 + 22t`. Let `H` be a finite indexed graph with `Q` edges and a **conventional graceful** labeling `g`: its vertex labels are distinct elements of `0,…,Q`, and its edge differences are exactly `1,…,Q`. Choose an actual vertex `r` of `H` with `g(r)=0`. Identify `r` with the midpoint of a path of `2K` edges. The two resulting path halves are distinct, named arms of `K` edges each; every original vertex and edge of `H` remains.

For each of the two arms, and separately for either depth `d₀` or `d₁` measured from `r`, the actual graft has a conventional graceful labeling with zero at that selected arm vertex. These are **four separate existence statements**, not one labeling putting zero at four vertices. The residual graph need not be a tree, connected, bipartite, or alpha labeled, and its vertex labels need not fill `0,…,Q`. The theorem does not prescribe zero at an old residual vertex, a new tip, or any other depth. At `t=1`, the arm length is 47 and the two depths are 42 and 43.

The formal entry point is [`GracefulBoundary.Q24Rooted.terminal_four`](source/Q24Rooted.lean). In its parameters `p=22+12(t−1)`, the graft is exactly `graftGraph (pathGraph (4*p+6)) H (center p) r`, with midpoint index `2*p+3=K`. The four targets are the path vertices `K−d₀`, `K−d₁`, `K+d₀`, and `K+d₁`; each `ZeroAt` conclusion contains its own witness.

## Construction and prior work

The q24 source gives an alpha-labeled `2K`-edge path with midpoint at the alpha boundary. Its left selected positions carry path labels zero and `2K`; reversal supplies the corresponding right positions. The graft retains the low path labels, shifts the high path labels by `Q`, and labels residual vertices from `g`. Residual edge weights remain `1,…,Q`; path weights become `Q+1,…,Q+2K`. Complementing the entire labeling handles a target that initially has the maximum.

The alpha/graceful vertex-amalgamation and high-side interval shift are established operations, not a new operation claimed here. Christian Barrientos, [“On the generation of alpha graphs,” *Journal of Algebra Combinatorics Discrete Structures and Applications* 9(2) (2022), 101–114](https://doi.org/10.13069/jacodesmath.1111733), states an alpha-plus-graceful amalgamation in the inspected introductory passage. The present q24 certificate controls the two specified interior positions on each new arm. The [bounded primary-literature audit](evidence/primary-literature-scope.md) does not establish worldwide priority or exhaustive non-overlap; **priority remains unknown**.

## Reproduction

The package contains exactly [60 Lean source files](SOURCE-SHA256SUMS.txt) and no OLEAN objects. Use Python 3.10+ and Lean 4.34.0. The verified Lean executable in the internal replay was SHA-256 `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`; another Lean 4.34.0 installation can be supplied for a fresh reproduction.

```text
python build.py --check
python -O build.py --check
python build.py --lean <path-to-lean-4.34.0> --output <new-directory-outside-this-package>
```

The build checks every packaged byte, source imports, and the [recorded build order](build-order.json). It creates its output directory only if that path is new, compiles every source with `warningAsError=true` and only its fresh object directory on `LEAN_PATH`, checks the exact theorem and axiom closures, compiles the [non-onto triangle instance](checks/Query.lean), and requires the [wrong-root, false-onto, and wrong-depth controls](checks/negative/) to fail at their intended contracts. Build objects and logs stay outside this source package. [`SHA256SUMS.txt`](SHA256SUMS.txt) inventories all package payload files except itself; its own hash identifies this version.

The [author freeze](evidence/author-report.md), [separate internal mathematical check](evidence/separate-math-report.md), and [separate copied-source Lean replay](evidence/separate-lean-report.md) retain their original bytes. The evidence folder also preserves the mathematical check code and normal/optimized results, plus the replay scripts and build/control results. Copied source and evidence may retain local execution paths or development-status comments from the original work; use `build.py` above for portable reproduction. [`provenance.json`](provenance.json) binds each copied source and selected evidence file to its original path and SHA-256. Evidence manifests describe their original audit folders; they are not this package's inventory.

## Methods, status, and version

AI tools assisted documented construction and proof development, checker and Lean code, literature comparison, translation preparation, and separately tasked internal checks. Jordi Gartner's publishing responsibility is distinct from those tasks. The mathematical and Lean checks are **internal project checks**, not external or peer review. The reader notes in [English](reader-note.en.md), [German](reader-note.de.md), and [simplified Chinese](reader-note.zh.md) preserve the same scope; the German and Chinese translations remain editorial drafts pending language review.

**Version 1** packages the arbitrary-rooted-residual four-target theorem, its exact source dependencies, reproducible build, semantic controls, and pinned internal evidence. No broader zero-position or priority claim is included.
