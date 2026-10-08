**Research note · Version 1 · 8 October 2026**

This note belongs to the [Three equal long arms: zero-rotatability at lengths three and four](https://beedbyte.tech/research/graceful-spider-three-arms) project.

## Statement and terminology

For `k` equal to 3 or 4 and any integer `m >= 1`, let `S_(k,m)=S(k,k,k,1^m)` be the tree with center `c`, three long arms `a_i1,...,a_ik` for `i=0,1,2` (in order away from `c`), and `m` additional leaves `p_0,...,p_(m-1)` adjacent to `c`. It has `q=3k+m` edges. A graceful labeling is a bijection from its vertices to `{0,...,q}` whose edge differences are `{1,...,q}`.

**Theorems A and B.** For each `k` in `{3,4}` and every integer `m >= 1`, `S_(k,m)` is 0-rotatable: given any vertex `v`, there is a graceful labeling with `f(v)=0`. The statement makes no claim for other `k`.

## Theorem A: five base certificates for arms of length three

For `k=3` and `m=1`, the following rows give one certificate for each vertex orbit. Each arm triple lists labels at depths 1, 2 and 3. `t` is the fixed insertion threshold used below. The column `d` is the difference of the edge to the next inserted leaf.

| Vertex carrying zero | `c` | Arm 0 | Arm 1 | Arm 2 | `p_0` | `t` | `d` |
| --- | ---: | --- | --- | --- | ---: | ---: | ---: |
| Center | 0 | (1,6,4) | (8,2,5) | (10,3,7) | 9 | 10 | 11 |
| Arm depth 1 | 8 | (0,10,1) | (2,9,4) | (6,7,3) | 5 | 2 | 6 |
| Arm depth 2 | 1 | (9,0,10) | (4,3,5) | (7,2,6) | 8 | 7 | 7 |
| Arm depth 3 | 9 | (1,10,0) | (2,5,6) | (3,8,4) | 7 | 1 | 8 |
| Center leaf | 10 | (1,3,8) | (2,9,5) | (4,7,6) | 0 | 0 | 10 |

Every row uses vertex labels `0,...,10` exactly once. For each row, classify an edge as *same-side* if both endpoint labels are at most `t` or both exceed `t`, and *crossing* otherwise. Direct calculation gives the following **disjoint** difference intervals; every difference within each interval occurs once.

| Zero orbit | Same-side differences | Crossing differences |
| --- | --- | --- |
| Center | 1,...,10 | empty |
| Arm depth 1 | 1,...,5 | 6,...,10 |
| Arm depth 2 | 1,...,6 | 7,...,10 |
| Arm depth 3 | 1,...,7 | 8,...,10 |
| Center leaf | 1,...,9 | 10 |

Thus each row is graceful. The exact checker and the independent audit in the package verify all individual edges as sorted lists, so duplicates are not hidden by set comparisons.

## Threshold-insertion lemma

Let a tree `T` have `q` edges, a graceful labeling `f`, a vertex `c` where a leaf will be attached, and a fixed integer `0 <= t <= q`. Set

`d=t+1-f(c)` if `f(c)<=t`, and `d=f(c)-t` if `f(c)>t`.

Suppose the same-side edges have differences `1,...,d-1` exactly once, while crossing edges have differences `d,...,q` exactly once. Insert a new leaf at `c`, shift each old label above `t` upward by one, and give the new leaf label `t+1`:

`f+(v)=f(v)+1_[f(v)>t]` for old vertices; `f+(new leaf)=t+1`.

The old labels become `0,...,t,t+2,...,q+1`; the new label fills the only gap. Old same-side differences stay fixed. Every old crossing difference rises by one. The new leaf edge has difference `d`. Hence the new differences are exactly `1,...,d-1`, `d`, and `d+1,...,q+1`, each once.

The interval hypothesis also persists with the **same threshold `t`**:

1. If `f(c)<=t`, the center remains low and the new leaf is high. Their edge is crossing with difference `d`. The same-side interval remains `1,...,d-1`; the shifted old crossing interval is `d+1,...,q+1`, so with the new edge it is `d,...,q+1`. The parameter `d` is unchanged.
2. If `f(c)>t`, the center rises by one and both center and new leaf lie above `t`. Their edge is same-side with difference `d`. The next parameter is `d'=d+1`; the same-side interval is `1,...,d` (equivalently `1,...,d'-1`), and the shifted crossing interval is `d'=d+1,...,q+1`.

The invariant can therefore be iterated for arbitrarily many new center leaves. The vertex carrying zero is unchanged: zero never exceeds `t`, and the new leaf gets the positive label `t+1`.

Apply this lemma repeatedly to each of the five length-three base rows. These rows cover the center, all three depths on a long arm, and a short center leaf. Permuting the three long arms or the short leaves moves any prescribed vertex into the corresponding row's zero position. This proves Theorem A for every `m >= 1`.

## Theorem B: six base certificates for arms of length four

For `k=4`, the same lemma applies to six different base rows at `m=1`, where `q=13`. Each arm quadruple lists vertex labels at depths 1 through 4. Every row uses all labels `0,...,13` exactly once and all edge differences `1,...,13` exactly once. The final two columns give the fixed threshold and next-leaf difference.

| Vertex carrying zero | `c` | Arm 0 | Arm 1 | Arm 2 | `p_0` | `t` | `d` |
| --- | ---: | --- | --- | --- | ---: | ---: | ---: |
| Center | 0 | (1,8,3,7) | (12,4,6,9) | (13,2,11,5) | 10 | 13 | 14 |
| Arm depth 1 | 10 | (0,13,1,12) | (2,11,4,5) | (6,8,3,9) | 7 | 2 | 8 |
| Arm depth 2 | 1 | (12,0,13,3) | (7,2,6,5) | (10,8,11,4) | 9 | 7 | 7 |
| Arm depth 3 | 11 | (1,12,0,13) | (2,5,6,8) | (3,10,4,9) | 7 | 1 | 10 |
| Arm depth 4 | 2 | (12,1,13,0) | (8,4,9,7) | (10,3,6,5) | 11 | 4 | 3 |
| Center leaf | 13 | (1,3,11,6) | (2,12,5,9) | (4,10,7,8) | 0 | 0 | 13 |

For these rows, the same-side differences are respectively `1,...,13`, `1,...,7`, `1,...,6`, `1,...,9`, `1,...,2`, and `1,...,12`. The crossing differences are the complementary consecutive intervals `d,...,13` (empty in the center row). Each individual difference occurs once, as checked in `k4_bases.json`, `k4_verify.py`, and the separate `audit-k4.md`.

The fixed-threshold lemma therefore extends all six rows to every `m >= 1`, preserving zero at its original vertex. The six orbits are the center, arm depths 1 through 4, and a short center leaf. Arm and short-leaf permutations cover every prescribed vertex. This proves Theorem B.

## Reproduction and review

The downloadable `graceful-spider-three-arms-proof.zip` contains both sets of base data, both exact verifiers (`verify_proof.py` and `k4_verify.py`), bounded search code, the two separate internal audits (`audit.md` and `audit-k4.md`), the source proof notes, the literature review, and `BUNDLE-README.md`. Its SHA-256 is `86b4e0f5c01a8f43a4579894e891a3ef362c675280ca70a75b9df790b064b549`. After unpacking, run `python verify_proof.py` and `python k4_verify.py`. Python 3.12.1 checked every base row and the interval invariant through `m=100` for both families on 8 October 2026. The unbounded theorems follow from the written lemma and complete orbit lists, not from those finite runs.

Independent internal AI audits reconstructed the base cases without importing the respective project verifiers and checked further finite invariant instances. Both report PASS for the mathematical constructions and their stated scope. These are elementary written proofs with computational certificate checks; neither has been formalized in a proof assistant, externally reviewed, or peer reviewed. Some source files retain sentences describing their historical pilot status; `BUNDLE-README.md` dates and explains those sentences.

## Prior work and priority

Patterson's 2017 thesis proposed a broader spider 0-rotatability conjecture (Conjecture 5.4.4), with an exceptional family. Its reported finite census covers some small cases in both families, but cannot establish all `m`. The thesis PDF could not be inspected page by page during this review, so the conjecture's exact wording should be checked from the original before a submission claiming originality. Rofa's 2023 result treats rooted symmetric trees and uniform-leg spiders, not directly these mixed-leg all-`m` families. Bahls, Lake, and Wertheim established gracefulness of related spider families; gracefulness alone is weaker than 0-rotatability. A related gap-insertion idea was publicly described before this work, and no novelty is claimed for that general idea.

The targeted literature review did not locate either exact all-`m` theorem. **Priority remains unresolved; this note does not claim a new conjecture, the first proof, or worldwide novelty.** The two theorems apply only to the specified families with long-arm lengths three or four.
