# Zero placement throughout the interior of a rooted graceful 119-edge-arm graft

**Beedbyte · source package v1**

Jordi Gartner publishes this work through Beedbyte. English is the source text; the German and simplified Chinese versions are translation drafts without recorded human language review.

## Fixed K119 theorem

Let `H` be any finite indexed graph with `Q` edges, supplied with a conventional graceful labeling `g` and a specified root `r` such that `g(r)=0`. Attach two new 119-edge arms by identifying their shared path midpoint, at index 119 of a 238-edge path, with `r`. For every integer depth `d` with `1≤d≤118`, each of the two named-arm vertices at path indices `119−d` and `119+d` can receive label 0 in a conventional graceful labeling of the entire graft. Each target has its own labeling. The edge-label span is `238+Q`.

The supplied root-zero labeling is a premise. `H` need not be connected, acyclic, a tree, onto-labeled, or alpha-labeled; `Q=0` is allowed. The conclusion does not cover the shared root, old vertices of `H`, either new tip at depth 119, or two targets simultaneously.

## All-r near-tip families

For every `r≥1`, put `K_r=30·4^r−1`. The copied source closure proves separate zero placements on either named new `K_r`-edge arm at the following four pairs of depths, for every supplied root-zero conventional graceful finite `H`:

| Source theorem | Depths |
|---|---|
| `TerminalNormalized.rooted_both` | `K_r−8`, `K_r−7` |
| `TerminalSeed56.rooted_both` | `K_r−6`, `K_r−5` |
| `TerminalSeed34.rooted_both` | `K_r−4`, `K_r−3` |
| `TerminalSeed12.rooted_both` | `K_r−2`, `K_r−1` |

Together these are the eight depths `K_r−8,…,K_r−1`, each with its own target-dependent labeling. This is a near-tip statement for those eight positions only; it does not prove full interior coverage for `r>1` or for every odd arm length. The fixed `K119Through118.expanded` theorem separately proves every interior depth 1–118 for `K=119`.

## Proof composition and earlier work

The fixed theorem composes the frozen `K119Through114.interior` result for depths 1–114 with the two terminal-seed families for 115–116 and 117–118. The older 1–114 coverage is retained unchanged in `source/K119Through114.lean`. The two new 59-entry seed words and their corrected source mappings are included in `evidence/`; no historical input record is rewritten.

The append used to extend terminal-normalized paths is an older endpoint-matched graceful-permutation concatenation, not a new operation. Its published ancestry includes the construction in the proof of [Hicks–Ollis–Schmitt, Lemma 4.5](https://community.middlebury.edu/~jschmitt/papers/HicksOllisSchmitt2018.pdf) and [Adamaszek, Lemma 1](https://arxiv.org/pdf/math/0608513). The generic alpha/root-zero graft is also prior work, stated in [Panpa, Imnang and Wasuanankul (2025), Theorem 2.5](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777) and [Shan–Zhong (2026), Lemma 1](https://arxiv.org/html/2605.14295v2). Applying [Shan–Zhong, Theorem 2](https://arxiv.org/html/2605.14295v2) twice already gives the arbitrary-`H` cases at depths 1 and 2 on either named arm; [Luiz–Campos–Richter (2017), Theorem 14](https://ic.unicamp.br/~reltech/2017/17-12.pdf) covers the one-central-leaf case. The older operations and these special cases are credited. Whether prior results imply the full K119 range 1–118 remains unresolved; worldwide priority is **UNKNOWN**.

## Reproduction and verification

The package contains all 68 Lean modules in the transitive source closure, the exact module order, and 19 check modules: 3 positive checks and 16 negative controls. `build.py` takes a caller-supplied Lean executable and a new output directory outside this package. It checks the pinned Lean 4.34.0 executable SHA256, verifies package source/check hashes, builds into fresh objects with warnings as errors, then runs `Support`, `Positive`, and `WholeClosure` plus 16 semantic mutants. `check_path_guard.py` tests output containment and existing/dangling symlink cases; `verify_package.py` checks file integrity. Run these Python scripts with `python -B` to avoid bytecode artifacts. No network or other project checkout is required.

The author build compiled all 68 sources and counted 2,809 theorem closures using only `propext`, `Classical.choice`, and `Quot.sound`. A separate copied-source replay recompiled all 68 modules, checked the five principal theorem heads, and rejected eight semantic false controls. The authored check suite additionally records 1,072 named cases and 16 effective semantic mutants. These are internal project checks, not external review or peer review. The Lean kernel, compiler, standard library and encoded graph definitions remain the formal trust boundary. Frozen author and replay reports are copied under `evidence/`.

## Methods and contributions

AI tools assisted the documented Lean implementation and reproduction/check scripts, and drafted the German and simplified Chinese translations. The formal proof and copied-source replay are separate internal project artifacts; neither is external review.

Version 1 adds a formal proof of separate zero placements at all interior depths 1–118 for K119 and records the all-r near-tip depth pairs `K_r−8,…,K_r−1`.
