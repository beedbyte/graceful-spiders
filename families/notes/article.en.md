# Prescribed zero in equal arm spider families of lengths 3, 5, 7, 9 and 11

**Research note · 2026-10-09.** The construction has passed a separate internal mathematical audit. Publication priority and external expert review remain unresolved. German and Chinese companion texts are translation drafts awaiting human language review.

For each `k∈{3,5,7,9,11}`, every integer `n≥2` and every integer `m≥0`, the tree `S(k^n,1^m)` is **0-rotatable**: any prescribed vertex can receive zero in a graceful labeling. An explicit center construction, a composition with an α-labeled path, a formula for odd arm lengths, and 10 finite path certificates give a proof for unbounded numbers of long arms and center leaves. The finite certificates supply the remaining interior positions; the parameter bounds follow from the written constructions.

This note belongs to the [Graceful spider project](https://beedbyte.tech/research/graceful-spider-three-arms). It strengthens the earlier [seven-edge three-arm note](https://beedbyte.tech/publications/seven-edge-three-arm-spider-zero-rotatability), whose scope was `k=7,n=3,m≥1`, by allowing arbitrary `n≥2` and including `m=0`. The earlier length-4 theorem, `S(4,4,4,1^m)` for every `m≥1`, remains a separate result. Nothing here extends that length-4 assertion to arbitrary arm counts.

## The theorem and its quantifiers

Write `S(k^n,1^m)` for the tree with a distinguished center `c`, `n` arms containing `k` edges each, and `m` further leaves adjacent to `c`. Superscripts denote multiplicities, not powers. A vertex at depth `j` on a long arm is `j` edges from `c`. The tree has `q=nk+m` edges and `q+1` vertices. The case `n=2,m=0` is a path with a distinguished midpoint; it is explicitly included even under conventions reserving “spider” for a tree with a branching vertex.

A graceful labeling is a bijection `f:V→{0,…,q}` such that the absolute endpoint differences on the edges use `1,…,q` exactly once.

**Theorem.** For every `k∈{3,5,7,9,11}`, every integer `n≥2`, every integer `m≥0`, and every vertex `v` of `S(k^n,1^m)`, there exists a graceful labeling `f` with `f(v)=0`.

The labeling may depend on `v`; the quantifiers are “for every vertex, there exists a labeling.” The theorem makes no claim for arbitrary odd lengths, even lengths, unequal long arms, or all spiders. It does not require the final labeling to be an α-labeling. An α-labeling is a graceful labeling with a threshold crossed by every edge.

**General partial result.** For every odd `k≥3`, every `n≥2` and every `m≥0`, zero can be prescribed at the center, at depths `1,2,k−1,k` on any long arm, or at any short leaf that exists. Coincident depths are counted once. We first prove this statement and then use the 10 certificates to complete the 5 lengths in the theorem.

## A formula placing zero at the center

For integers `k≥1,h≥0,m≥0`, consider `S(k^h,1^m)`. Give its center label zero. Index the long arms by `i=0,…,h−1` and depths by `j=1,…,k`, and put

```text
b(i,j) = (h−i)k − (j−1)/2    if j is odd,
b(i,j) = ik + j/2            if j is even.
```

Give the short leaves labels `hk+1,…,hk+m`. This specializes the established root labeling for symmetric trees; the direct verification also handles the extra center leaves.

In each block `[ak+1,(a+1)k]`, for `a=0,…,h−1`, the first `⌊k/2⌋` labels are the even-depth labels on arm `a`; the last `⌈k/2⌉` are the odd-depth labels on arm `h−1−a`. Consequently the long arms use exactly `1,…,hk` once.

Center edges have differences `(h−i)k`, all positive multiples of `k` through `hk`. The internal differences on arm `i` are

```text
|(h−2i)k−s|,    1≤s≤k−1.
```

Write `u=h−2i`. These form `[bk+1,(b+1)k−1]`, with `b=u−1` when `u>0` and `b=−u` when `u≤0`. The positive values of `u` give `b=h−1,h−3,…`; the nonpositive values give the remaining parity in increasing order. Together the `b` values are exactly `0,…,h−1`. Thus these internal blocks and the multiples of `k` partition `1,…,hk`. The short-leaf differences fill `hk+1,…,hk+m`, proving gracefulness.

The formula remains valid when `h=0`: only a star remains. When `h=m=0`, the tree is a single vertex. When `k=1`, the internal difference blocks are empty. These cases matter because the composition below can have a residual tree with no long arms.

## Composition with an alpha path

Let `H=P_(2k+1)` have positions `0,…,2k`, with the designated center at position `k`. Suppose `a` is an α-labeling with threshold `A`, and require `a(k)=A`. Every edge joins a label at most `A` to a label above `A`. Let `G=S(k^(n−2),1^m)` have the center-zero labeling `b` just proved, and set `Q=(n−2)k+m`.

Identify the centers of `G` and `H`. On the resulting tree define

```text
f(v)=b(v)+A          on G,
f(v)=a(v)            on H when a(v)≤A,
f(v)=a(v)+Q          on H when a(v)>A.
```

Both rules give `A` at the identified center. The residual tree occupies `[A,A+Q]`; the low path labels occupy `[0,A]`; the high path labels occupy `[A+Q+1,2k+Q]`. Their only shared label is `A` at the same vertex, so the combined labeling uses exactly `0,…,nk+m`.

The residual differences remain `1,…,Q`. Every path edge crosses the threshold, so each path difference increases by `Q`, giving `Q+1,…,Q+2k`. These disjoint intervals give all differences `1,…,nk+m` once.

The path vertex with label zero stays zero. The path vertex with label `2k` becomes the overall maximum `nk+m`. Complementing all labels by `x↦nk+m−x` preserves edge differences and makes that maximum vertex zero. Hence any depth occupied by zero or `2k` in the path supplies a prescribed zero depth for every `n≥2,m≥0`. Permuting whole equal arms transports that position to any selected arm. This is the established α-amalgamation construction with the locations of its extreme labels retained; no new composition method is claimed.

For `n=2,m=0`, we have `Q=0`, and the residual graph is one vertex. The construction is precisely the original path. For `n=2,m>0`, the residual graph is a star with `m` leaves. Thus neither boundary introduces an assumption about a branching center.

## An odd length formula for depths 1 and 2

Let `k=2r+1` with `r≥1`, and give the path midpoint label `A=2r`. Read each arm from the midpoint outward. Define

```text
a_L(2j+1)=4r+2−j,    0≤j≤r,
a_L(2j)=j−1,         1≤j≤r,
a_R(2j+1)=2r+1+j,    0≤j≤r,
a_R(2j)=2r−j,        1≤j≤r.
```

The low labels comprise the center `2r`, the left even-depth labels `0,…,r−1`, and the right even-depth labels `r,…,2r−1`. The high labels are the disjoint intervals `[3r+2,4r+2]` on the left and `[2r+1,3r+1]` on the right. Each edge crosses `A=2r`.

The right-arm differences, from the center outward, are `1,2,…,2r+1`. The first left difference is `2r+2`; the others are `4r+2,4r+1,…,2r+3`. Thus every difference `1,…,4r+2=2k` occurs once. The maximum `2k` is at left depth 1 and zero at left depth 2. Composition and complementation therefore give both depths for every odd `k≥3`, throughout the stated ranges of `n,m`.

## Tips and short leaves

If a graceful tree has `q` edges and a specified zero vertex, attach a leaf there with label `q+1`. Old differences stay unchanged and the new difference is `q+1`. Complement the labels about `q+1`. The new leaf now has zero, and its predecessor has the maximum. This elementary reversible leaf construction is an established ingredient.

To place zero at the tip of a selected long arm, start with center-zero `S(k^(n−1),1^m)`. Apply the operation `k` times, each time at the current zero endpoint. This grows the missing arm and gives zero at depth `k`. Its predecessor has label `nk+m`; another complement gives zero at depth `k−1`. The starting graph exists for `n=2` as well.

For a selected short leaf, when `m≥1`, start with center-zero `S(k^n,1^(m−1))` and apply the operation once. Permuting the short leaves puts zero at whichever one was prescribed. At `m=0`, there is no short-leaf case to check. Together with the center construction and the odd path formula, this proves the general partial result.

## The 10 path certificates and complete depth coverage

Each tuple below lists a path from one endpoint to the other. Its entry at index `k`, counting from zero, is the midpoint and has label `A=k−1`. The final columns are distances from the midpoint to zero and to `2k`.

| k | Path labels | Zero depth | Maximum depth |
| ---: | --- | ---: | ---: |
| 5 | `(9,1,10,0,7,4,5,3,8,2,6)` | 2 | 3 |
| 7 | `(12,3,13,1,14,0,11,6,7,5,8,4,10,2,9)` | 2 | 3 |
| 7 | `(10,1,14,0,12,2,13,6,7,5,8,4,9,3,11)` | 4 | 5 |
| 9 | `(15,3,16,2,17,1,18,0,11,8,9,7,13,4,14,6,10,5,12)` | 2 | 3 |
| 9 | `(16,2,17,1,18,0,13,4,10,8,9,6,14,3,15,5,12,7,11)` | 4 | 5 |
| 9 | `(17,1,18,0,15,4,12,7,9,8,11,5,14,2,16,3,13,6,10)` | 6 | 7 |
| 11 | `(18,4,19,3,20,2,21,1,22,0,13,10,11,9,14,7,16,8,12,6,17,5,15)` | 2 | 3 |
| 11 | `(19,3,20,2,21,1,22,0,15,6,16,10,11,9,12,8,13,5,17,4,18,7,14)` | 4 | 5 |
| 11 | `(20,2,21,1,22,0,17,3,19,4,14,10,11,9,12,6,18,5,16,7,15,8,13)` | 6 | 7 |
| 11 | `(21,1,22,0,19,2,20,4,16,7,13,10,11,9,14,6,17,3,18,5,15,8,12)` | 8 | 9 |

Every tuple uses `0,…,2k` once and alternates across `A=k−1`. The consecutive edge differences are:

| k | Zero depth | Edge differences |
| ---: | ---: | --- |
| 5 | 2 | `(8,9,10,7,3,1,2,5,6,4)` |
| 7 | 2 | `(9,10,12,13,14,11,5,1,2,3,4,6,8,7)` |
| 7 | 4 | `(9,13,14,12,10,11,7,1,2,3,4,5,6,8)` |
| 9 | 2 | `(12,13,14,15,16,17,18,11,3,1,2,6,9,10,8,4,5,7)` |
| 9 | 4 | `(14,15,16,17,18,13,9,6,2,1,3,8,11,12,10,7,5,4)` |
| 9 | 6 | `(16,17,18,15,11,8,5,2,1,3,6,9,12,14,13,10,7,4)` |
| 11 | 2 | `(14,15,16,17,18,19,20,21,22,13,3,1,2,5,7,9,8,4,6,11,12,10)` |
| 11 | 4 | `(16,17,18,19,20,21,22,15,9,10,6,1,2,3,4,5,8,12,13,14,11,7)` |
| 11 | 6 | `(18,19,20,21,22,17,14,16,15,10,4,1,2,3,6,12,13,11,9,8,7,5)` |
| 11 | 8 | `(20,21,22,19,17,18,16,12,9,6,3,1,2,5,8,11,14,15,13,10,7,4)` |

Each difference tuple is a permutation of `1,…,2k`, so these are directly checkable α-path certificates. Composition supplies their zero depths, and complementation supplies their maximum depths.

| k | Depths from the general constructions | Further depths from certificates | Total long-arm coverage |
| ---: | --- | --- | --- |
| 3 | 1,2,3 | none | 1,…,3 |
| 5 | 1,2,4,5 | 3 | 1,…,5 |
| 7 | 1,2,6,7 | 3,4,5 | 1,…,7 |
| 9 | 1,2,8,9 | 3,4,5,6,7 | 1,…,9 |
| 11 | 1,2,10,11 | 3,4,5,6,7,8,9 | 1,…,11 |

For `k=11`, the four additional paths have midpoint label `A=10` and certify zero/maximum depth pairs `(2,3)`, `(4,5)`, `(6,7)` and `(8,9)`. Put `Q=11(n−2)+m`. The composition uses intervals `[0,10]`, `[10,10+Q]` and `[11+Q,22+Q]`, with only the shared center repeated before identification. Its difference intervals are `1,…,Q` and `Q+1,…,Q+22`. Thus the four paths supply depths `2,…,9` for every `n≥2,m≥0`. The odd formula with `r=5` supplies depth 1, while leaf extension supplies depths 10 and 11. The four certificates therefore complete the eleven-edge family, including the path case `n=2,m=0`; this is a proved finite-length extension, not an extrapolation to larger odd lengths.

The center and every existing short leaf are already covered. Whole-arm permutations put each depth construction on any prescribed long arm. This covers every vertex and completes the theorem. It does not rely on claiming that this list gives exactly the automorphism orbits in every degenerate case.

## The limit of this alpha path route

For even `k=2r≥2`, no graceful labeling of `P_(2k+1)` has midpoint label `k` and maximum `2k` on a neighbor of that midpoint. In the specified α-path reduction, the midpoint's low bipartition class has `k+1` vertices, forcing its α-index to be `k`. Zero also cannot be on a neighboring vertex, since that vertex is on the high side. Consequently this route cannot supply depth-1 zero for even `k`.

The obstruction follows by forcing the largest differences: the arm must start `2r,4r,0,4r−1,1,4r−2,2,…,3r+1,r−1`. Each competing pair for the next large difference uses an already saturated path vertex; the midpoint cannot realize a difference above `2r`. After `2r` edges the endpoint `r−1` is reached. The remaining labels together with the midpoint lie in `[r,3r]`, whose width is `2r`, and cannot realize the still missing difference `2r+1`. The full induction is in the [source proof](../proof.md) and passed the separate audit.

This is an obstruction to the specified composition route. It does not establish a failure of 0-rotatability for even-arm spiders; the separate length-4 theorem illustrates why those claims must remain distinct.

## Established results and unresolved priority

Ordinary gracefulness of the whole equal-arm family, even for other `k`, follows from the established center-zero construction and adding center leaves with successive maximum labels. Center zero, α-amalgamation, and reversible leaf extension therefore have prior sources. Patterson's 2017 thesis presents these ingredients at Corollary 2.4.3 and Theorems 3.2.1 and 5.3.6, attributing amalgamation to Huang–Kotzig–Rosa (1982). Its Conjecture 5.4.4 already places the present families within a broader spider 0-rotatability question. See the [institutional thesis](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content).

Several entire boundary families already have prescribed-zero coverage:

| Parameters | Earlier coverage |
| --- | --- |
| `n=2,m=0`, every `k` | Path 0-rotatability, restated in Luiz–Campos–Richter Lemma 4 and Shan–Zhong Lemma 2 |
| `n=2,m=1`, every `k` | Luiz–Campos–Richter (2017), Theorem 14: a path with a leaf at a central vertex |
| `n=2,k=3`, every `m≥0` | Luiz–Campos–Richter, Theorem 22: every diameter-6 caterpillar |
| `k=3,m=0`, every `n≥2` | Rofa (2023), Corollary 3: symmetric spiders of leg length at most 3 |

For the diameter-6 row, the 2 long arms form a path and extra center leaves preserve its diameter and caterpillar structure. The cited theorem numbers belong to the [2017 university report IC-17-12](https://ic.unicamp.br/~reltech/2017/17-12.pdf); they are not assigned here to the related 2020 journal article. Rofa's [original paper](https://arxiv.org/pdf/2312.16235) treats symmetric spiders and leaves lengths at least 4 open. Its symmetric-root hypotheses do not directly cover the mixed family `k=3,n≥3,m≥1`.

Panpa–Imnang–Wasuanankul (2025), Theorems 3.2–3.4, give center zero for 3 legs, prescribed-leaf zero for 4 legs, and gracefulness for 5 legs. “5 legs” means total legs. These statements do not supply all interior zero positions for arbitrary arm counts. See their [original paper](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777). Shan–Zhong (2026), Theorem 5, gives gracefulness when all but 3 arms have length at most 2; Lemma 1 restates the α-amalgamation used here. See [version 2](https://arxiv.org/html/2605.14295v2).

The focused literature audit for the first four lengths and the separate `k=11` primary-source cross-check did not locate a full two-parameter prescribed-zero theorem for `k=5,7,9,11` in the sources they checked. For `k=11`, the path cases `n=2,m=0` and the central-leaf cases `n=2,m=1` are already covered by the same earlier path and caterpillar results. The diameter-6 theorem concerns the `k=3` row; two eleven-edge arms instead have diameter 22. This supports a comparison with those sources, not a claim of first proof. Original texts from 1977 and 1982, the full Cattell paper, simultaneous prescribed-label path results, and complete citation chains remain incompletely checked. Earlier tables or stronger composition results could subsume these applications. Publication priority for the theorem, the finite certificates, and the method is unresolved.

## Reproduction and independent internal checks

The [source package](../README.md) separates the two audited scopes. The [first proof](../proof.md), [six certificates](../certificates.json), `construct.py`, `verify.py` and the first independent checker concern `k∈{3,5,7,9}`. The [eleven-edge proof](../k11/proof.md), [four additional certificates](../k11/certificates.json), `k11/check.py` and the [k11 independent audit](../k11/independent/AUDIT.md) concern `k=11`. The combined theorem follows from these two proofs and the ten exact paths printed above.

A [proof ZIP](../REPRODUCIBILITY.md) contains the same `families/` tree. From the repository root, or from the extracted directory containing `families/`, run:

```sh
python -B families/verify.py
python -B families/independent/verify_independent.py
python -B families/k11/check.py
python -B families/k11/independent/verify_independent.py
python -B families/construct.py 9 3 1 5
```

The last command prints a labeling for `S(9^3,1^1)` with zero at depth 5 on a representative arm. That supplied constructor's supported lengths remain `3,5,7,9`; it is not a constructor API for `k=11`. For its supported lengths it exposes `prescribed_zero(k,n,m,target)`, with center `'c'`, long-arm vertex `('a',i,j)` and short leaf `('p',s)`, where `0≤i<n`, `1≤j≤k`, `0≤s<m`. The independent k11 verifier builds actual labelings at every requested vertex in its test matrix, including centers, short leaves, tips and interior arm vertices.

For the first four lengths, the original checker records 1,440 center-formula checks, 100 odd-path checks, six certificates, 652 representative labelings, 2,352 exact-zero checks, and two rejected corruptions. Its separate audit uses its own vertex representation and independently written construction. It imports neither the original checker nor the search program; a second track uses the supplied constructor only to produce witnesses.

| Separate internal check for `k∈{3,5,7,9}` | Recorded scope |
| --- | --- |
| Center formula | 5,376 checks; `k=1,…,64`, `h=0,…,20`, `m∈{0,1,7,50}` |
| Odd path formula | 200 checks; odd `k=3,…,401` |
| Finite certificates | six |
| Exact zero vertex, own implementation | 16,368 checks |
| Exact zero vertex, supplied implementation | 16,368 checks |
| Full vertex test matrix | `k∈{3,5,7,9}`, `n=2,…,12`, `m=0,…,7` |
| Large parameters | 208 checks across both implementations; `(n,m)=(2,10000),(1000,0),(100,100)` |
| Negative controls | three rejected cases: duplicate labels, wrong zero vertex, wrong α-threshold |
| Even-route finite diagnostic | six permutations for `k=2`; 5,040 for `k=4` |

For `k=11`, the supplied `check.py` separately records four exact certificates, 1,680 composed labelings with the zero checked at an exact arm vertex, and two rejected corruptions. Its grid uses `n∈{2,3,4,5,8,20}`, `m∈{0,1,2,5,30}`, both extremes of each certificate, and every arm. A further internal agent audit independently checked the proof and implemented center, tip, short-leaf and interior constructions without importing the code under review.

| Separate internal check for `k=11` | Recorded scope |
| --- | --- |
| Center-zero examples | 84, including the one-vertex residual graph |
| Finite certificates | all four; label, difference, threshold, midpoint and extreme-depth checks |
| Exact prescribed vertices | 7,172; every vertex for `n=2,…,12`, `m=0,…,7` |
| Path boundary | all 23 vertices at `n=2,m=0` |
| Large-parameter compositions | 48; `(n,m)=(2,10000),(1000,0),(100,100)`, all four paths, both extremes, selected arms 0 and `n−1` |
| Negative controls | three rejected corruptions of certificates or extreme-depth claims |

All recorded checks pass. These are separate reports with stated scopes, not counts from a single combined test run. The checkers use Python 3.10 or later and the standard library. Run them in a writable copy because some write result files. The supplied `verify.py` and `k11/check.py` use assertions and must be run without optimization (`-O`); the independent verifiers use explicit errors. The [reproduction guide](../REPRODUCIBILITY.md) documents the release files and checks.

Search code is not needed to verify the printed witnesses. The k11 search fixes midpoint label 10, the zero and maximum positions, and the alpha sides. Its reported successful large-run counts were not independently reproduced by the mathematical auditor. A budget cutoff means `UNKNOWN`, not nonexistence, and any completed restricted exhaustion would apply only to those chosen constraints. No exhaustive search claim is used in the proof. The infinite quantifiers follow from the interval argument and complete depth coverage.

## AI work and review status

AI agents developed the α-path reduction and odd-length formula, searched for the first six finite certificates, wrote the constructor and original multiset checker, and prepared the source proof. The original construction and checker were produced in the same research session. A separate AI agent reviewed the mathematical argument, implemented a second construction and checker without importing the search or original checker, and tested exact prescribed vertices in both implementations. Another separate AI review checked primary-source hypotheses and the older boundary-family overlap. A later AI-assisted search produced the four eleven-edge certificates, and a separate agent reviewed that extension and implemented its own verifier without importing the search or supplied checker. AI drafted the present combined English and German texts from those proofs and reports.

These are specific internal research and audit activities. The original separate mathematical audit accepted the four-length theorem, general partial result and narrowly scoped even-route obstruction. The later audit accepted the `k=11` extension and its union with those four lengths, finding no omitted vertex or parameter restriction. Its independence concerns separate implementation and review within the AI workflow. No external mathematician's review, peer review or proof-assistant formalization has been completed. The German companion text remains a translation draft awaiting human language review. The project owner retains the release decision; this note makes no novelty or priority claim.

The four extra witnesses settle the eleven-edge case within this construction. The remaining mathematical question is whether, for every odd `k≥3` and every even depth `d` with `2≤d≤k−3`, an α-labeled `P_(2k+1)` can have midpoint label `k−1`, zero at depth `d`, and maximum `2k` at depth `d+1`. A uniform construction meeting that condition would extend the proof to all odd arm lengths. No such construction is proved here.
