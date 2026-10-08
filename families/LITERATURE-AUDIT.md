# Literature scope audit: adapted public report

9 October 2026. This focused primary-source comparison is not an exhaustive priority determination. This public adaptation omits the raw report's historical workspace status and changes its outdated editorial instruction to describe the corrected packaged literature note. The mathematical comparisons and source links are retained. Raw-report provenance is recorded in `SOURCE-MANIFEST.json`.

## Finding

Ordinary gracefulness of the entire family, including arbitrary k, is already a consequence of a uniform-spider center-zero labeling followed by adding center leaves. The composition and reversible leaf constructions are established ingredients. The additional mathematical assertion under review concerns every prescribed interior zero position. No checked primary source states the full two-parameter k=5,7,9 result. This search does not establish its novelty. All four families lie in the scope of Patterson's older conjecture; the m=0 uniform families also lie in Rofa's conjectural scope.

The packaged `literature.md` acknowledges the older n=2 boundary results below. An undifferentiated statement that all inner positions for k=5,7,9 are additional coverage is too broad.

## Exact overlaps

| Parameters or positions | Checked older coverage | Meaning |
|---|---|---|
| All k, n, m; center zero | Symmetrical-tree root-zero construction, reproduced as Panpa et al. Theorem 2.4; append leaves with successive maximum labels | Entire family's gracefulness is known |
| n=2, m=0, every k | Path zero-rotatability; Rosa/Cattell, explicitly restated by Shan–Zhong Lemma 2(a,b) | Every vertex is already covered, including k=9 |
| n=2, m=1, every k | Luiz–Campos–Richter (2017), Theorem 14, central vertex of a path identified with a vertex of K2 | Every vertex is already covered, including k=5,7,9 |
| k=3, n=2, every m | Luiz–Campos–Richter Theorem 22: every diameter-six caterpillar | Every vertex is already covered |
| k=3, m=0, every n | Rofa Corollary 3: symmetric spiders of leg length at most three | Every vertex is already covered |
| Any k, n>=2, m>=0; tips, their predecessors, short leaves | Center-zero construction plus Patterson Theorem 5.3.6 and complementation | Known ingredients give these positions; this is a deduction, not a verbatim family theorem |
| k=5,7,9, remaining parameter range | No full prescribed-zero theorem located in checked originals | Potential additional coverage relative to these sources; priority unresolved |

For k=3 with n>=3,m>=1 the root at the distinguished center is not a symmetric root: its first level contains both leaves and internal vertices. Rofa's Corollary 3 therefore cannot directly be cited for this mixed family. For k=5,7,9 it does not apply even when m=0. The n=2,m=0 graph is a path with a distinguished midpoint, so spider-definition conventions should be stated explicitly.

## Primary sources and hypotheses

**Patterson (2017), thesis.** The institutional original and existing local extraction were checked at Corollary 2.4.3, Theorems 3.1.3, 3.2.1, 3.3.8, 5.3.6 and Conjecture 5.4.4. Uniform spiders have center zero; alpha amalgamation is attributed to Huang–Kotzig–Rosa (1982). Theorem 3.3.8 gives gracefulness for at most three arms longer than one, with alpha gracefulness when some arm exceeds two. Theorem 5.3.6 ties a prescribed zero leaf to center zero after removal of its whole arm. The conjecture proposes zero-rotatability for spiders outside S(3,1,1,...), which includes every present family with at least two long arms. Its order-at-most-16 census supplies finite data, not the unbounded theorem. [Institutional PDF](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content).

**Rofa (2023), arXiv:2312.16235.** Corollary 3 on printed page 12 proves symmetric-spider zero-rotatability only for leg lengths <=3. The summary explicitly leaves symmetric leg lengths >=4 for investigation. Theorem 1 supplies root-zero labeling; Theorem 2 has rooted-symmetry and caterpillar-remainder hypotheses and supplies selected final levels, not arbitrary depths of every uniform spider. Thus k=9 is anticipated conjecturally, not proved by the paper. [Original PDF](https://arxiv.org/pdf/2312.16235), [record](https://arxiv.org/abs/2312.16235).

**Luiz–Campos–Richter (2017), IC-17-12.** Theorem 14 (printed page 6) proves zero-rotatability of a path with one leaf attached to a central vertex. Theorem 22 (printed pages 16–17) covers every diameter-six caterpillar. These give the boundary deductions in the table. The report also restates Rosa's path theorem in Lemma 4 and distinguishes it from prescribing a second label. None of these statements controls both the midpoint alpha index and a prescribed zero elsewhere, as required by the reduction. [Original university technical report](https://ic.unicamp.br/~reltech/2017/17-12.pdf). The related 2020 article should be checked separately before assigning its theorem numbers to these 2017 statements: [publisher DOI](https://doi.org/10.1007/s00373-020-02226-0).

**Panpa–Imnang–Wasuanankul (2025).** Theorem 2.4 restates uniform center-zero; Theorem 2.5 states the exact alpha-amalgamation rule used in the proof. Theorem 3.2 gives center zero for three legs; 3.3 gives any leaf zero for four legs; 3.4 proves gracefulness of five-legged spiders. These do not assert all interior zero positions for arbitrary arm counts. The original wording is five total legs; do not copy Shan–Zhong's introductory paraphrase as a verified five-nontrivial-leg result. [Publisher full text](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777).

**Shan–Zhong (2026), v2.** Lemma 1 restates Huang–Kotzig–Rosa's amalgamation. Lemma 2(a,b) supplies path zero-rotatability, with only the alpha midpoint exception at P5. Theorem 5 gives gracefulness when all but three legs have length <=2, covering n<=3 here. It does not quantify arbitrary prescribed zero vertices. [Original full HTML](https://arxiv.org/html/2605.14295v2).

**Bahls–Lake–Wertheim (2010).** Theorem 1 gives gracefulness when leg lengths belong to {r,r+1}; it covers uniform spiders, not directly mixed {1,k} for k>=3. The paper expressly says its theorem follows from Poljak–Sura (1982). It makes no complete prescribed-zero assertion. [Publisher PDF](https://msp.org/involve/2010/3-3/involve-v3-n3-p01-p.pdf).

**Niu (2026), withdrawal.** The arXiv record confirms withdrawal on 14 May 2026 for lack of novelty of uniform center-zero plus routine pendant extension. Its v1 treated only ordinary gracefulness of three-edge arms with center leaves. Do not use its surviving abstract's novelty language. [Original withdrawal record](https://arxiv.org/abs/2605.02303).

## Recommended public wording

“We give an explicit certificate-and-composition proof that S(k^n,1^m) is zero-rotatable for k in {3,5,7,9}, n>=2 and m>=0, where n counts k-edge arms and m counts center leaves. The proof uses established center-zero, alpha-amalgamation and leaf-extension constructions. Several subfamilies, including the path cases, the two-arm cases with one center leaf, and the uniform three-edge-arm cases, are already covered by earlier results. The family belongs to the scope of older zero-rotatability conjectures. Publication priority is unresolved, and independent expert review is pending.”

For k=9 specifically: “The construction covers nine-edge equal arms with arbitrary arm and center-leaf counts. We have not located the full statement in the primary sources checked; this is not a claim of first proof.”

Avoid “new graceful family”, “new composition method”, “first proof”, “settles spider zero-rotatability”, or an assertion that k=9 was previously unanticipated. Preserve the finite k restriction and the distinction between internal certificates and external review.

## Remaining historical gap

Searches included zero/0-rotatability, zero-ubiquitous gracefulness, uniform and symmetric spiders, prescribed path labels, five/seven/nine-edge legs, Rosa's *Labelling snakes*, and Huang–Kotzig–Rosa's *Further results on tree labellings*. The original 1977 and 1982 full texts were not obtained; their exact attributions were checked through accessible authors' sources. Cattell's publisher abstract was obtained, but its full text and the precise classification of simultaneous prescribed labels remain unchecked. Earlier path tables or more general label-preserving composition theorems could subsume the certificates. A complete backwards/forwards citation-chain review remains necessary before any priority claim.
