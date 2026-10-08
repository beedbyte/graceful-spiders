# Independent k=11 mathematical audit: public adaptation

9 October 2026. Adapted from the separately conducted agent audit. Historical workspace/publication-status lines were omitted and the reproduction command made relative. Substantive mathematical findings and review limits are retained. Original-source hashes appear in `../SOURCE-MANIFEST.json`.

## Decision

**GO for the mathematical statement:** For every integer n>=2, every integer m>=0, and every prescribed vertex v of S(11^n,1^m), a graceful labeling exists with v labeled zero. The n=2,m=0 case means the path on 23 vertices with its midpoint distinguished. There is no omitted arm depth or parameter restriction in the argument.

Together with the previously audited k in {3,5,7,9} theorem, this supports the mathematical union k in {3,5,7,9,11}.

**NO-GO for novelty, first-proof, arbitrary-odd-k, or universal-spider claims.** The ingredients are known, prior boundary families overlap, and publication priority remains unresolved. This is a separately implemented agent audit, not an external mathematical referee report or proof-assistant verification.

## Exact finite certificates

All four rows were read from JSON and checked without importing the supplied search, checker, or construction. Each is a permutation of 0,...,22; adjacent differences have multiplicity exactly one for 1,...,22; each edge crosses threshold 10; position 11 is labeled exactly 10. Their zero/maximum positions are respectively (9,8), (7,6), (5,4), (3,2), giving distances (2,3), (4,5), (6,7), (8,9) from the midpoint. Thus all depths 2 through 9 are certified. Exact edge-difference lists are saved in `verification.json`.

The midpoint class has 11 vertices, consistent with low labels 0,...,10; the other class has 12 vertices. No alternative alpha-index convention is being assumed.

## All-parameter proof audit

Write h=n-2>=0 and Q=11h+m. The residual graph has h long arms and m center leaves. The center-zero formula in the earlier proof is valid including h=0 and h=m=0. Its labels partition into blocks of eleven: the first five labels of a block come from the even depths of one arm, and its last six from the odd depths of the reverse-indexed arm. Its center edges give the positive multiples of eleven. Internal differences on arm i are |11(h-2i)-s| for 1<=s<=10. For h-2i>0 these occupy the block immediately below that multiple; for h-2i<=0 they occupy the block immediately above its absolute value. The resulting block indices are exactly 0,...,h-1, split by parity. Thus no differences coincide or vanish. Short leaves supply 11h+1,...,Q.

Identifying its zero center with the certified path midpoint labeled 10, shifting all residual labels by 10, and shifting only path labels greater than 10 by Q gives the intervals [0,10], [10,10+Q], and [11+Q,22+Q]. Their sole shared label is the identified center. The resulting label set is exactly 0,...,22+Q=11n+m. Residual edge differences are 1,...,Q; every path difference increases by Q, producing Q+1,...,Q+22. This establishes gracefulness algebraically for all n,m.

The path zero remains zero. The path maximum becomes 11n+m, so complementing all labels makes that vertex zero. A whole-arm permutation transfers it to any prescribed arm. This explicitly controls the selected vertex, rather than merely providing one vertex of each type.

When n=2,m=0, Q=0 and the residual graph is the single identified midpoint; the construction reduces to the same certified path. When n=2,m>0, the residual graph is a star. Neither case requires a positive number of residual long arms.

The earlier odd-path formula with r=5 proves depths 1 and 2, with midpoint 10. Its right differences are 1,...,11; its left differences are 12 followed by 22,21,...,13. It has maximum 22 at depth 1 and zero at depth 2. The same interval argument therefore supplies depth 1, which the four new paths alone do not supply.

Depths 10 and 11 follow by deleting the selected long arm, using a center-zero labeling, and attaching eleven successive vertices. At each step attach the new maximum label at the old zero vertex and complement. The new endpoint is zero; its predecessor has the overall maximum. After eleven steps these are depths 11 and 10. A final complement supplies depth 10. This argument works for n=2 as well. For any specified short leaf, remove that leaf first and apply the same operation once; m-1 is nonnegative precisely when that target exists. Center zero is already provided by the formula.

Consequently the coverage is: center; depths 1 through 11 on every arm; and every short leaf. These exhaust the graph's vertices. The proof has no hidden appeal to tests, search exhaustion, or an unproved family for larger k.

## Independent computations and code limits

Run `python -B verify_independent.py` from this directory.

- Four exact alpha-path certificates and the separately generated depth-1/2 formula passed.
- 84 center-zero examples passed, including the one-vertex residual graph.
- 7,172 prescribed-vertex checks passed: every vertex of every k=11 graph with n=2,...,12 and m=0,...,7. All 23 vertices at n=2,m=0 were individually checked.
- 48 large-parameter composition checks passed for (n,m)=(2,10000),(1000,0),(100,100), all four certificates, both extrema, and selected arms 0 and n-1.
- Three corrupted certificates or extremum-depth claims were rejected.
- The supplied `check.py` was also executed normally and passed its stated 1,680 checks and two negative cases.

The independent code uses named vertices, its own graph construction, block-based center-label generation, direct placement of the selected path half, and explicit runtime failures. It imports no implementation under review. It implements center, short-leaf, and long-tip constructions as well as intermediate-depth composition, so coverage is tested by actual labelings rather than a hard-coded depth union.

The supplied `check.py` uses Python assertions, which disappear under `python -O`; its documented ordinary invocation works. The independent verifier remains active under optimization. This is a tooling limitation, not a mathematical defect.

The search code is internally consistent for these k=11 calls. JavaScript shifts through bit 22 fit the signed 32-bit representation. It fixes zero and maximum on adjacent positions, checks the initialized labels and parity, fills a frontier of the connected path with unused labels, and rejects repeated edge differences. A filled path is therefore a certificate under the selected constraints. A budget-10 smoke test returned UNKNOWN at node 11, correctly distinguishing a cutoff from exhaustion. The reported large-run node counts and exact search transcripts were not independently reproduced. They are not needed for existence once the witnesses are independently checked. EXHAUSTED would apply only to the fixed midpoint, parity, and extremum-position constraints, and this solver is not validated for arbitrary k.

## Literature overlap and priority

Patterson's 2017 original thesis extraction was read at Corollary 2.4.3, Theorems 3.2.1 and 5.3.6, and Conjecture 5.4.4. It provides uniform center-zero, alpha composition, reversible leaf growth, and an older spider zero-rotatability conjecture encompassing this family. The underlying 1982 composition attribution is reported through this thesis; the 1982 original was not obtained. [Institutional thesis](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content).

The primary 2017 Luiz-Campos-Richter report was checked directly. Lemma 4 supplies every prescribed zero on paths, so n=2,m=0 is already established for k=11. Theorem 14 covers a path with a leaf added at a central vertex, so n=2,m=1 is also already established. These are complete prescribed-zero overlaps, not merely ordinary gracefulness. The report's diameter-six result does not supply k=11, whose two-long-arm diameter is 22. [Original report](https://ic.unicamp.br/~reltech/2017/17-12.pdf).

Rofa's original paper was checked at Corollary 3 and its summary. Its full symmetric-spider result is for leg length at most three; it does not state a complete k=11 theorem. It supports known ingredients and older conjectural context, not priority for this audit's result. [Original paper](https://arxiv.org/pdf/2312.16235).

Shan-Zhong's Theorem 5, checked in the original v2, concerns ordinary gracefulness when all but three arms have length at most two. It supplies no complete prescribed-zero statement for unbounded arm counts. Ordinary gracefulness of this entire uniform-plus-leaves family is already a consequence of the known center-zero construction. [Original v2](https://arxiv.org/html/2605.14295v2).

This was a focused primary-source cross-check, not an exhaustive literature or citation-chain search. A theorem about simultaneous prescribed labels in alpha paths or earlier path tables may subsume these four witnesses or their application. The defensible description is an explicit internally checked certificate-and-composition proof for k=11 using known ingredients, with known boundary overlaps and unresolved publication priority.
