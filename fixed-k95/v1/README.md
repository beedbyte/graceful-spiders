# Zero-rotatability of spiders with 95-edge arms

**Beedbyte — source package v1**

Jordi Gartner publishes this work through Beedbyte. [Deutsch](README.de.md) · [简体中文](README.zh-CN.md)

## Theorem

For every integer `n ≥ 2`, `m ≥ 0`, and every actual vertex v of `S(95^n,1^m)`, there is a graceful labeling with v labeled zero. The graph has one hub, n named arms of exactly 95 edges, and m original hub leaves. Each target gets a separate labeling; labels are exactly `0,…,95n+m` and edge differences exactly `1,…,95n+m`. This includes the hub, every named arm at physical depths 1..95, and every existing short leaf. When m=0 there is no short-leaf target. No theorem for other odd arm lengths is asserted.

The Lean entry point is `GracefulBoundary.K95Full.all_vertices`; `unique_zero` also identifies the selected vertex as the only zero. See [K95Full.lean](source/K95Full.lean), the [all-depth map](coverage.md), and the [exact catalog](data/lean-catalog.json).

## Proof and verification

Fifty-one midpoint-alpha P191 words cover arm depths 1..94. Their complete label/difference inventories, cut 94, midpoint index 95 labeled 94, and selected extrema are checked in Lean. Established alpha amalgamation with an explicit root-zero residual transfers each word to all n,m and each named arm; maximum-derived cases use whole-graph complement. Explicit constructions handle the hub, original leaves and actual tip 95.

Status: **separate internal mathematical QA GO; Lean author build GO; separate copied-source Lean replay GO.** The author compiled 35 source modules with Lean 4.34.0 and warnings as errors, checked 1678 standard-only theorem axiom closures, 671 named examples and 12 semantic controls. The later [separate replay](evidence/separate-lean-replay.md) rebuilt all 35 modules, checked eight specified theorem closures, 13 examples and eight semantic controls. The mathematical aggregate audit uses a separate implementation and universal transfer proof. These checks are internal, not external or peer review.

This package contains source only, with no compiled objects. The trust boundary includes Lean's kernel/executable and standard library, the graph definitions and their mathematical interpretation. Selected frozen reports and original manifests are in [evidence](evidence/); those manifests describe their original audit directories, not this package inventory. Reports retain the status at their freeze date; the current verification above incorporates later records. Copied origins and hashes are in [provenance.json](provenance.json).

## Prior results and limits

Older alpha amalgamation, graceful-permutation insertion and concatenation are credited, including [Hicks–Ollis–Schmitt, Lemma4.5's proof](https://community.middlebury.edu/~jschmitt/papers/HicksOllisSchmitt2018.pdf), [Adamaszek, Lemma1](https://arxiv.org/pdf/math/0608513), and [Ollis, Lemma5.5/Theorem5.6](https://ajc.maths.uq.edu.au/pdf/78/ajc_v78_p035.pdf). The H1 branch uses an older concatenation operation. [Luiz–Campos–Richter, Lemma4/Theorem14](https://ic.unicamp.br/~reltech/2017/17-12.pdf) already covers every vertex of the `n=2,m=0/1` subfamilies. Lemma5 is ordinary graceful one-point freedom, not a joint midpoint/alpha/extreme prescription.

Worldwide priority remains **UNKNOWN**. The [bounded comparison](evidence/bounded-priority.md) records additional overlaps and the unresolved [Cattell2007](https://doi.org/10.1016/j.disc.2007.03.046) full-text gap. Neither missing access nor a new project catalog establishes novelty.

## Reproduction and contributions

Use Python 3.10+ and Lean 4.34.0; no solver is required:

```
python build.py --check
python verify_catalog.py
python -O verify_catalog.py
python build.py --lean /path/to/lean --output /new/directory/outside/this/package
```

The builder checks all SHA256SUMS.txt payload hashes, compiles in dependency order, and uses only its fresh output directory on LEAN_PATH. AI tools assisted the documented source construction, proof development, coding, Lean formalization, literature comparison and internal checks. These roles are distinct from Jordi Gartner's publishing responsibility. These translated reader notes have internal consistency checks, not documented external language review.

Version 1 supplies the fixed-k95 theorem, complete interior catalog, boundary/tip sources, source reproduction tools and selected evidence.
