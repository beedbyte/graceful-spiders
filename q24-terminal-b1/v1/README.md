# Two prescribed zero positions on an unbounded family of spiders

**Beedbyte — source package v1**

Jordi Gartner publishes this work through Beedbyte.

## Theorem

Let `t ≥ 1`, `k = 23 + 24t`, `n ≥ 2`, and `m ≥ 0` be integers. Form `S(k^n,1^m)` from a hub, `n` paths of exactly `k` edges meeting only at that hub, and `m` additional hub leaves. On any selected long arm, each of the depths

```
20 + 22t       21 + 22t
```

can receive label zero in a graceful labeling. The two positions use separate labelings. Graceful means that vertex labels are exactly `0,…,nk+m` and absolute edge differences are exactly `1,…,nk+m`. Depth is distance from the hub.

The Lean statement is `GracefulBoundary.Q24Terminal.terminal_actual` in [Q24Terminal.lean](source/Q24Terminal.lean). It quantifies over every selected named arm and includes `n=2, m=0/1`. Examples are `k=47` at depths `42/43`, `k=95` at `86/87`, and `k=143` at `130/131`. This theorem does not assert full zero-rotatability at these lengths.

## Proof and sources

A fixed three-chain certificate reverses the order of two extreme labels in a midpoint alpha path. Apply any number of the previously proved q24 steps, then apply this terminal adapter once. An alpha/residual amalgamation transfers the path to the actual spider, retaining every original leaf. Whole-graph complementation gives one of the two zeros. See the [proof outline](proof-outline.md), [literal certificate](data/gadget.json), and [34 Lean sources](build-order.json).

The underlying alpha-amalgamation and related concatenation operations have older antecedents. In particular, the old H1 append reduces to [Hicks–Ollis–Schmitt, Lemma 4.5's proof](https://community.middlebury.edu/~jschmitt/papers/HicksOllisSchmitt2018.pdf) with alpha rotation, and to [Adamaszek, Lemma 1](https://arxiv.org/pdf/math/0608513). These comparisons do not classify every possible composition that could subsume this terminal adapter. Worldwide priority of the exact positional result remains **unknown**.

The subfamilies `n=2,m=0` and `n=2,m=1` are already covered by [Luiz–Campos–Richter, Lemma 4 and Theorem 14](https://ic.unicamp.br/~reltech/2017/17-12.pdf). Their Lemma 5 states ordinary graceful one-vertex/one-label freedom; it is not a simultaneous midpoint/alpha/extreme prescription. The full original [Cattell pi-representation paper](https://www.sciencedirect.com/science/article/pii/S0012365X07001215) remains a full-text access gap in this project's bounded comparison. No novelty conclusion follows from that gap.

## Reproduction and verification

Use Python 3.10+ and Lean 4.34.0. No solver or third-party Python library is needed.

```
python build.py --check
python verify_gadget.py
python -O verify_gadget.py
python build.py --lean /path/to/lean --output /new/directory/outside/this/package
```

The build verifies all indexed bytes and local imports, then compiles with `warningAsError=true` into a new external directory. Only that fresh directory is placed on `LEAN_PATH`. This package contains no OLEAN objects. `SHA256SUMS.txt` covers every payload file except itself; its own digest identifies this version in the release record.

The [separate internal mathematical check](evidence/separate-math-check.md) verifies the all-parameter construction and named-graph transfer. The [separate copied-source Lean replay](evidence/separate-lean-replay.md) compiled all 34 modules from source, checked the 18 new theorem axiom closures, six concrete named-vertex instances, and six effective negative controls. The new theorem closures use only `propext`, `Classical.choice`, and `Quot.sound`, or subsets. The trust boundary includes Lean's kernel and executable, its standard library, the graph definitions and their mathematical interpretation. This is internal project verification, not external or peer review.

[TerminalQuery.lean](checks/TerminalQuery.lean) and the [negative controls](checks/negative/) are preserved from that replay. Historical reports retain their original status text; the later replay report records completion of the earlier pending replay. [Provenance](provenance.json) binds every copied source and evidence file to its original path and digest.

The evidence directory contains selected original reports, manifests and query/control logs. The original manifests describe their larger private audit directories; they are provenance records, not this package's inventory. Use this package's `SHA256SUMS.txt` to verify the distributed files.

## Methods and contributions

AI tools assisted the documented gadget construction, symbolic proof development, checker implementation, Lean formalization, literature comparison, and separately tasked internal checks. Jordi Gartner's publishing responsibility is distinct from these documented contributions.

## Version 1

Contains the terminal B1/D23/A24 certificate, universal two-depth theorem, actual-spider transfer, source reproduction tools, and verification records. No broader zero-position theorem is included in the formal entry point.
