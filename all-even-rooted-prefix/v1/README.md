# Prescribed zero positions on even arms of a rooted graceful graph

**Beedbyte · source package v1**

Jordi Gartner publishes this work through Beedbyte.
[Deutsch](README.de.md) · [简体中文](README.zh.md). The German and Chinese texts are translation drafts without recorded human language review.

## The theorem

Let **K ≥ 20 be even**. Let H be a finite graph with Q edges and a supplied conventional graceful labeling g: its vertex labels are distinct integers in 0,…,Q and its edge differences are exactly 1,…,Q. A specified root r must satisfy g(r)=0. Attach two distinct new K-edge arms at r, retaining H.

For **either named new arm** and every depth **2 ≤ d ≤ D8(K)**, there is a separate conventional graceful labeling of the resulting graph with zero at that vertex. Depth is the number of edges from r. The labeling may change with the target; simultaneous zeros are not asserted.

| Even K | D8(K) |
|---|---|
| 20–34 | 11 |
| 36–52 | 27 |
| 54–124 | 25 + 16⌊(K−35)/18⌋ |
| K ≥ 126 | 107 + 20a + 2s, where (K−4)/2 = 61 + 11a + s and 0 ≤ s ≤ 10 |

H need not be a tree, connected, bipartite or alpha-labeled. Its vertex labels need not fill 0,…,Q. A root-zero labeling is an assumption, not a consequence of bare gracefulness. The theorem makes no claim for old vertices of H, depth 1, the tips, or depths beyond D8(K); it does not assert full zero-rotatability of every graft.

## Proof and prior work

The construction supplies an alpha labeling of the 2K-edge path with cut K, midpoint label K, and an extreme label at the chosen position. It then labels H by K+g, retains path labels below K, and shifts path labels above K by Q. Old edge differences are 1,…,Q; new differences are Q+1,…,Q+2K. Reversal selects the other arm and whole-graph complement converts a maximum target to zero.

The generic alpha-cut/root-zero amalgamation is established prior art, attributed to Huang–Kotzig–Rosa and stated explicitly in [Panpa, Imnang and Wasuanankul (2025), Theorem 2.5](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777) and [Shan–Zhong (2026), Lemma 1](https://arxiv.org/html/2605.14295v2). See also [Barrientos (2022), *On the generation of alpha graphs*, p.103](https://www.jacodesmath.com/index.php/jacodesmath/article/view/194), 9(2), 101–114, DOI 10.13069/jacodesmath.1111733. Paired zero/boundary anchors already appear in [Barrientos–Minion (2019), §2.2](https://digitalcommons.georgiasouthern.edu/tag/vol6/iss1/4/).

Worldwide priority for this exact uniform midpoint/D8 certificate family and its corollary is **UNKNOWN**. The inspected sources do not settle possible subsumption by older constructions. The complete original [Cattell (2007) alpha-path characterization](https://doi.org/10.1016/j.disc.2007.03.046) was inaccessible in this comparison; separate one-position freedoms do not by themselves prove the joint midpoint/extreme condition. No new generic graft operation or negative graph theorem is claimed here.

## Reproduction and trust boundary

The principal theorem is `GracefulBoundary.EvenRootedPrefix.all_even_prefix` in [EvenRootedPrefix.lean](source/EvenRootedPrefix.lean). The package contains all 79 transitive project sources and nine separately written query/control sources. It requires Python 3.9+ and Lean **4.34.0** with its bundled standard libraries; no other project checkout is needed.

```text
python build.py --check
python -O build.py --check
python build.py --lean /path/to/lean --output /new/outside/package/build
```

The output directory must not exist. The driver verifies every indexed payload, compiles all modules into fresh objects with warnings as errors, checks 3,583 theorem axiom closures, expands the actual graph theorem, and runs 16 named triangle cases and seven expected-failure controls. K=20,36,124,126 and a residual triangle labeled 0,1,3 test boundaries and the non-onto convention. Failed depth/root/tip/onto controls test theorem assumptions, not graph impossibility. No compiled objects are distributed.

The universal statement is proved in Lean; the finite examples alone do not establish it. Trust includes the correspondence between the definitions and the stated graph, Lean's kernel/toolchain and the accepted axioms `propext`, `Classical.choice`, `Quot.sound`. A separate internal copied-source replay passed. These are internal project checks, not external review or peer review. [Provenance](provenance.json) records exact source and evidence hashes; full historical reports remain in the project archive.

## Methods and contributions

AI tools assisted the documented proof development, Lean implementation, separate internal replay, literature comparison and these translation drafts. Publication responsibility rests with Jordi Gartner through Beedbyte.

Version 1 supplies the all-even D8 theorem, complete Lean source dependencies and reproducible scope checks.
