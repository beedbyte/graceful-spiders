# A certificate proof of 0-rotatability for S(7,7,7,1^m)

For every integer `m ≥ 1`, the spider tree `S(7,7,7,1^m)` is **0-rotatable**: any chosen vertex can receive zero in a graceful labeling. Five explicit base labelings, four complements, and an elementary rule for adding leaves give a proof for every `m`. The written proof and a separately implemented internal checker have been reviewed locally. Publication priority remains unresolved.

The tree has one center, three paths of seven edges starting at that center, and `m` additional leaves adjacent to the center. It has `q=21+m` edges and `q+1=22+m` vertices. A graceful labeling is a bijection from the vertices to `{0,…,q}` such that the absolute differences across the edges use every integer in `{1,…,q}` exactly once. For each chosen zero vertex, a different labeling is allowed. The theorem does not say that one labeling places zero at several vertices.

This note belongs to the existing [Graceful spider project](https://beedbyte.tech/research/graceful-spider-three-arms). Its previously released note treats arm lengths three and four. The result proved here has arm length seven and at least one additional center leaf. It makes no assertion for `m=0`, arbitrary arm lengths, other numbers of long arms, or all spiders. It also makes no assertion that every chosen zero vertex admits an α-labeling.

## A small certificate for an infinite family

It suffices to handle nine vertex types: the center, depths 1 through 7 on a long arm, and a short center leaf. The center is the unique vertex of degree greater than two. Distance from the center distinguishes the seven depths; degree distinguishes a short leaf from depth 1 on a long arm. Permutations of the three long arms and of the short leaves move vertices within each type. These are exactly the nine vertex orbits under graph automorphisms.

Here are five base certificates at `m=1`, when `q=22`. Each arm tuple lists labels from the center outward. `p₀` is the original short leaf. An edge is on the **same side** of the threshold `t` if both labels are at most `t` or both exceed `t`; otherwise it **crosses** the threshold. Write `c` for the center label and set `d=c-t` if `c>t`, and `d=t+1-c` otherwise.

| Zero vertex | c | Arm 0 | Arm 1 | Arm 2 | p₀ | t | d |
| --- | ---: | --- | --- | --- | ---: | ---: | ---: |
| Short leaf | 22 | (1,21,2,20,3,19,4) | (8,5,12,11,16,10,14) | (9,17,7,18,6,15,13) | 0 | 0 | 22 |
| Depth 1 | 20 | (0,22,1,19,3,17,9) | (8,14,13,6,4,21,2) | (5,18,7,16,11,15,12) | 10 | 2 | 18 |
| Depth 3 | 20 | (2,19,0,22,1,21,5) | (6,3,18,7,9,14,13) | (10,16,4,17,8,15,11) | 12 | 1 | 19 |
| Depth 5 | 19 | (2,20,1,21,0,22,6) | (4,3,15,9,14,11,13) | (5,18,10,17,7,16,12) | 8 | 2 | 17 |
| Depth 7 | 19 | (3,20,2,21,1,22,0) | (4,7,16,8,14,12,13) | (5,18,6,17,10,15,11) | 9 | 3 | 16 |

Every row uses `0,…,22` once. Its edge differences, including the edge from the center to the first entry of each arm, are `1,…,22` once. The following lists allow a direct check without running a program.

| Zero vertex | Arm 0 differences | Arm 1 differences | Arm 2 differences | Short-leaf edge |
| --- | --- | --- | --- | ---: |
| Short leaf | (21,20,19,18,17,16,15) | (14,3,7,1,5,6,4) | (13,8,10,11,12,9,2) | 22 |
| Depth 1 | (20,22,21,18,16,14,8) | (12,6,1,7,2,17,19) | (15,13,11,9,5,4,3) | 10 |
| Depth 3 | (18,17,19,22,21,20,16) | (14,3,15,11,2,5,1) | (10,6,12,13,9,7,4) | 8 |
| Depth 5 | (17,18,19,20,21,22,16) | (15,1,12,6,5,3,2) | (14,13,8,7,10,9,4) | 11 |
| Depth 7 | (16,17,18,19,20,21,22) | (15,3,9,8,6,2,1) | (14,13,12,11,7,5,4) | 10 |

For each base, replacing every label `x` by `22-x` preserves the differences. Replacing its threshold by `21-t` swaps the two threshold sides and preserves `d`. These complements supply the center and depths 2, 4, and 6. In the depth-1, depth-3, and depth-5 rows, the maximum label 22 occurs at depths 2, 4, and 6 respectively; those positions become zero under complementation. All thresholds used here lie in `0,…,21`, so the complemented thresholds remain valid for the zero-preserving construction below.

| Zero orbit | Obtained from | c | t | d | Same-side differences | Crossing differences |
| --- | --- | ---: | ---: | ---: | --- | --- |
| Center | Complement of short leaf | 0 | 21 | 22 | 1,…,21 | 22 |
| Depth 1 | Direct row | 20 | 2 | 18 | 1,…,17 | 18,…,22 |
| Depth 2 | Complement of depth 1 | 2 | 19 | 18 | 1,…,17 | 18,…,22 |
| Depth 3 | Direct row | 20 | 1 | 19 | 1,…,18 | 19,…,22 |
| Depth 4 | Complement of depth 3 | 2 | 20 | 19 | 1,…,18 | 19,…,22 |
| Depth 5 | Direct row | 19 | 2 | 17 | 1,…,16 | 17,…,22 |
| Depth 6 | Complement of depth 5 | 3 | 19 | 17 | 1,…,16 | 17,…,22 |
| Depth 7 | Direct row | 19 | 3 | 16 | 1,…,15 | 16,…,22 |
| Short leaf | Direct row | 22 | 0 | 22 | 1,…,21 | 22 |

The interval entries mean that every listed difference occurs exactly once. This stronger condition, beyond gracefulness alone, makes the extension work.

## The leaf-insertion lemma

Let a tree with `Q` edges have a graceful labeling `b` and a distinguished vertex with label `c`. Choose an integer `0≤t≤Q`, and define `d` as above. Suppose its same-side differences are exactly `1,…,d-1` and its crossing differences are exactly `d,…,Q`, each once.

For any integer `n≥0`, attach `n` new leaves at the distinguished vertex. On every old vertex set

`f(v)=b(v)` if `b(v)≤t`, and `f(v)=b(v)+n` if `b(v)>t`.

Give the new leaves labels `t+s`, for `1≤s≤n`. The old low labels, new labels, and old high labels occupy the disjoint intervals `[0,t]`, `[t+1,t+n]`, and `[t+n+1,Q+n]`. Thus every label from zero to `Q+n` occurs once. The original zero remains at the same vertex.

Old same-side edge differences remain `1,…,d-1`. Old crossing differences increase by `n` and become `d+n,…,Q+n`. If `c>t`, the distinguished vertex receives label `c+n`, so the new leaf differences are

`(c+n)-(t+s)=d+n-s`.

If `c≤t`, their differences are

`(t+s)-c=d+s-1`.

In either case, as `s` ranges from 1 to `n`, these differences use the missing interval `d,…,d+n-1` exactly once. For `n=0` that interval is empty. The three difference intervals are disjoint and together give `1,…,Q+n`. This proves the lemma for every `n`, directly.

Apply it to each of the nine bases with `Q=22` and `n=m-1`. The resulting tree is `S(7,7,7,1^m)` and the chosen base zero survives. Permuting arms or short leaves transfers zero to every vertex of its orbit. This proves the stated 0-rotatability for every `m≥1`.

For example, use the depth-1 row and take `m=3`. Shift its labels above 2 upward by 2, and attach leaves labeled 3 and 4. The center becomes 22. The new differences are 19 and 18, the old same-side differences remain `1,…,17`, and the old crossing differences become `20,…,24`. Zero is still at depth 1. This example illustrates the formula; the lemma supplies the unbounded conclusion.

## What was already known

Gracefulness of this entire family is covered by **Brandon J. Patterson's 2017 master's thesis**, Theorem 3.3.8, which in fact gives α-gracefulness when there are at most three legs longer than one and at least one longer than two. An α-labeling is a graceful labeling with a threshold crossed by every edge. Its existence does not specify an arbitrary zero vertex. Patterson's Conjecture 5.4.4 proposes 0-rotatability for spiders outside the family `S(3,1,1,…)`; the present family is a particular case of that older conjecture. The full 104-page thesis is available in the [Ball State repository](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content).

Several zero positions also follow from Patterson's earlier results. Remove a chosen seven-edge arm. The two remaining long arms form `P₁₅`, whose center admits zero under the path result quoted as Theorem 3.1.3. Attach the short leaves using new maximum labels; the remaining spider still has center zero. The reversible leaf reduction in Theorem 5.3.6 reconstructs the removed arm with zero at its tip. The tip's neighbor must then have the maximum label, because only an edge joining zero and the maximum can have difference `q`. Complementing yields zero at depth 6. These are deductions from the cited results, not a family theorem quoted verbatim from the thesis. Center zero and short-leaf zero also follow from known center-zero constructions and elementary leaf additions. Patterson's finite census covers order at most 16; the smallest tree here has 23 vertices.

**Panpa, Imnang, and Wasuanankul (2025)** prove center-zero labelings for three-legged spiders (Theorem 3.2), zero at any prescribed leaf for four-legged spiders (Theorem 3.3), and gracefulness for five-legged spiders (Theorem 3.4). The four-leg result applies directly to the leaves when `m=1`; the five-leg result applies to gracefulness when `m=2`. These statements do not provide all seven arm-depth zero positions for every `m`. See their [original paper](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777).

**Shan and Zhong (2026)** give gracefulness when all but three legs have length at most two (Theorem 5). This includes every tree in the present family. The cited statement asserts gracefulness and does not assert zero at every chosen vertex. See [arXiv:2605.14295v2](https://arxiv.org/abs/2605.14295v2).

Against these explicitly checked statements and deductions, the present certificate proof covers the five further inner depths 1 through 5 as part of all nine orbits. This comparison is not a proof of originality. Neither the theorem's publication priority, the base tables' priority, nor the general label-gap method is claimed here. The [source list](../SOURCES.md) records the wider comparison and the limits of the literature review.

## Reproduce the checks

The proof archive preserves the original file layout. From its extracted root, with Python 3.10 or later and no additional packages, run:

```sh
cd repro
python research-audits/graceful-k7-feasibility/verify-continuation.py
python research-audits/graceful-k7-independent/independent_check.py
```

The first checker verifies all nine bases, their threshold intervals, exact affine edge formulas, the reduced tip witness, and 900 concrete labelings for `m=1,…,100`. Its final summary includes `9 of 9 zero-label orbits verified; reduced tip witness PASS.`

The second checker reconstructs the graph from leg lengths with a different vertex representation. It imports neither the original checker nor the search programs. It checks the label and edge multisets, exact formulas for all nonnegative insertion counts, 54 explicit extensions, and 74 transfers of zero to every vertex for `m=1,2,5`. It also checks a deliberately wrong threshold and smaller-tree diagnostic cases. It ends with `GO for mathematical statement; novelty not assessed.` It writes `audit-results.json` beside itself, so an extracted copy needs write permission.

The JSON certificates and both checkers are sufficient for checking the bases; running the searches is unnecessary. The formulas and the interval proof establish the statement for all `m`; the finite diagnostics help detect coding or transcription errors. The [reproduction manifest](../REPRO-MANIFEST.json) records file hashes, and the [verification report](../REPRO-REPORT.md) records the checks. The [proof archive](../graceful-k7-zero-rotatability-proof.zip) contains the nine reproduction files.

AI assistance contributed to searches, proof development and checking, code checks, preparation of the text, and the German and Chinese translation drafts. The separate checker and mathematical review are internal; they are not external peer review or formal proof-assistant verification. The German and Chinese texts remain translation drafts.
