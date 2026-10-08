# Primary-literature boundary

Checked 9 October 2026. This is a focused comparison, not an exhaustive priority search. No novelty, first-proof, or new-method claim is made. The theorem under consideration is prescribed-zero labeling of `S(k^n,1^m)` for `k in {3,5,7,9}`, all `n>=2,m>=0`.

## Patterson (2017)

Brandon J. Patterson, *New Classes of Graceful Spiders and Related Computational Results*, master's thesis, Ball State University. [Institutional full text](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content). The audit consulted a local full-text extraction at the relevant passages; the institutional original is linked above.

Corollary 2.4.3 gives center-zero for uniform spiders. Theorem 3.2.1 gives the alpha-amalgamation construction and attributes the composition result to Huang–Kotzig–Rosa (1982). Theorem 5.3.6 gives the reversible center-zero/leaf-zero construction. These are existing ingredients, not new contributions of this note. Theorem 3.3.8 covers gracefulness with at most three nontrivial arms; it does not quantify arbitrary zero vertices. Conjecture 5.4.4 proposes zero-rotatability outside the exceptional `S(3,1,1,...)` family. The present theorem has at least two long arms and falls within that older conjectural scope. Its finite census reaches order 16 and cannot establish the unbounded `n,m` theorem. The original 1982 paper itself was not obtained here; its historical attribution is reported through Patterson and Shan–Zhong, whose versions of the construction were checked.

## Luiz–Campos–Richter (2017): established boundary subfamilies

Atílio G. Luiz, C. N. Campos, R. Bruce Richter, *Some families of 0-rotatable graceful caterpillars*, Technical Report IC-17-12, August 2017. [Original institutional PDF](https://ic.unicamp.br/~reltech/2017/17-12.pdf). Its Lemma 4, Theorem 14, and Theorem 22 establish the following overlaps:

- `n=2,m=0`: `S(k^2)=P_(2k+1)` is a path. Lemma 4 states Rosa's path-zero result, including the ordinary graceful exception to alpha-labeling at the midpoint of `P5`; the reference is Rosa, *Labeling snakes* (1977).
- `n=2,m=1`: `S(k,k,1)` is obtained by attaching one leaf to the midpoint of `P_(2k+1)`. Theorem 14 proves zero-rotatability of precisely this construction, for arbitrary `k`.
- `n=2,k=3`, arbitrary `m>=0`: `S(3,3,1^m)` is a caterpillar of diameter six, so Theorem 22 applies.

These are prior prescribed-zero results, not merely gracefulness statements. They must be excluded from any proposed additional coverage. The original theorem statements were checked directly; the full technical report was not independently re-proved.

## Rofa (2023)

Rafael I. Rofa, *0-rotatability of classes of rooted symmetric trees. Are rooted symmetric trees 0-rotatable?*, [arXiv:2312.16235](https://arxiv.org/abs/2312.16235), [original PDF](https://arxiv.org/pdf/2312.16235).

Theorem 1 gives an algebraic graceful labeling for rooted symmetric trees. Section 1 of the present proof is its uniform-spider specialization, directly verified here. The paper proves zero-rotatability for symmetric spiders of leg length at most three (Corollary 3), so the present `k=3,m=0` case is already covered. It explicitly asks about symmetric spiders of leg length four or greater. Its general rooted-tree results supply selected terminal levels, not all arm depths for arbitrary equal lengths. The abstract's conjectural language is not a proved universal spider theorem. No conclusion of publication priority follows from this comparison.

## Panpa–Imnang–Wasuanankul (2025)

A. Panpa, S. Imnang, T. Wasuanankul, *Graceful Labeling of Spider Graphs With at Most Five Legs*, [original publisher full text](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777).

Theorem 3.2 gives center-zero labelings for three-legged spiders. Theorem 3.3 gives a labeling with zero on any chosen leaf of a four-legged spider. Theorem 3.4 proves gracefulness for five-legged spiders. These statements handle overlapping center, leaf, or ordinary-existence cases. They do not state arbitrary-inner-vertex zero-rotatability for unbounded numbers of arms. Their known alpha-composition ingredient is closely related to the present reduction; using it is not a new-method claim.

## Shan–Zhong (2026)

Songling Shan and Yucheng Zhong, *Graceful Labeling of Two Families of Spiders*, [arXiv:2605.14295v2](https://arxiv.org/abs/2605.14295v2), [full HTML](https://arxiv.org/html/2605.14295v2).

The paper restates Huang–Kotzig–Rosa's alpha-amalgamation result and proves further gracefulness constructions. Its Theorem 5 covers all spiders with all but three legs of length at most two. That includes the three-long-arm specialization of the present result, as a statement of gracefulness. It does not cover arbitrary `n>3` through that theorem, nor assert all prescribed zero positions. The whole present family is nevertheless already graceful by the much older uniform center-zero construction plus new maximum labels on short leaves; even beyond Theorem 5, gracefulness itself is not a contribution here.

## Search limits and concrete status

Searches included symmetric/uniform spiders with zero-rotatability, arbitrary/odd leg lengths, alpha paths with prescribed center or zero positions, and the Huang–Kotzig–Rosa composition attribution. Relevant technical claims above were checked in the original thesis or authors' papers, not inferred from search snippets. No complete citation-chain review was done. In particular, prescribed pairs of labels in alpha paths, later zero-rotatability papers, and earlier finite path tables could subsume these applications or certificates.

The justified description is: a complete certificate-and-composition proof of the stated two-parameter families, using known composition and center/leaf constructions, with priority unresolved. The family includes the already established boundary subfamilies listed above. For `k=5,7,9`, potential additional prescribed-zero coverage relative to the specifically checked statements must exclude at least `n=2,m=0` and `n=2,m=1`; the present argument treats the remaining parameters uniformly as well. The `n=2,k=3` subfamily is already covered for every `m`. Even this narrowed comparison is not a worldwide originality claim.
