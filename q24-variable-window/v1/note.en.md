# A widening zero-label interval for equal-arm spiders

**Beedbyte.** Jordi Gartner publishes this work through Beedbyte.

For every integer t≥0, set k=23+24t. For every n≥2, m≥0, named long arm a, and depth d with 17+20t≤d≤20+22t, the actual vertex at depth d on arm a in S(k^n,1^m) can receive zero in a graceful labeling. Each arm-depth target may use its own labeling. The interval contains 4+2t depths: it is 37–42 when k=47 and 57–64 when k=71. The statement covers these depths only, not every vertex at those arm lengths.

The construction starts with two 47-vertex midpoint-alpha path labelings and extends them using the q24 B2 and B4 grafts in any order. Their zero positions yield two depth ranges that meet or overlap, and together cover the full interval. The path labelings transfer to two selected arms of the actual spider; a residual construction completes the graceful labeling over all remaining arms and original center leaves. This gives the same depth range for all n≥2 and m≥0.

At t=0 the interval lies within the previously proved all-vertex k=23 case. For every t, the path subfamilies n=2,m=0 and n=2,m=1 are also covered by earlier path results: Rosa’s path result as restated by Luiz, Campos, and Richter, and their Theorem 14 for a path with one center leaf. The proof uses classical alpha-amalgamation, restated by Shan and Zhong, as prior construction machinery.

Methods: AI tools assisted with developing the mixed B2/B4 construction and Lean proof; Lean 4.34.0 checks the frozen formal theorem.

Checks by separate AI agents are internal project checks, not external peer review.

## Sources

- [Luiz, Campos, and Richter, report IC-17-12, Lemma 4 and Theorem 14 (path cases).](https://ic.unicamp.br/~reltech/2017/17-12.pdf)
- [Shan and Zhong, Graceful Labeling of Two Families of Spiders, Lemma 1 (classical alpha-amalgamation).](https://arxiv.org/html/2605.14295v2)
- [Beedbyte, fixed-k23/v1 research note (prior full k=23 case, source revision b7546e3aac1a25e6a62c1a9eeb8794049ad093ed).](https://github.com/beedbyte/graceful-spiders/blob/b7546e3aac1a25e6a62c1a9eeb8794049ad093ed/fixed-k23/v1/note.en.md)
