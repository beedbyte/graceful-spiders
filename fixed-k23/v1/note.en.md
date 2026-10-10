# Every vertex of the fixed 23-edge-arm spider

Beedbyte. Jordi Gartner owns and publishes this work through Beedbyte.

For every `n ≥ 2` and `m ≥ 0`, each actual named vertex of `S(23^n,1^m)` can separately receive zero in a graceful labeling. This includes the hub, every depth on every named 23-edge arm, and each existing unit leaf. A different labeling may be used for each target. The result concerns fixed arm length 23; it does not assert the same conclusion for all odd arm lengths.

The proof combines complete midpoint-alpha paths on 47 vertices with a center-zero residual and the established alpha-amalgamation. Explicit certificates cover the fixed-length depths that older project constructions had not supplied. The path case `n=2,m=0` follows from Rosa's path result, and the central-leaf case `n=2,m=1` follows from Luiz–Campos–Richter; the Huang–Kotzig–Rosa amalgamation operation is classical. The full original Cattell path construction has not been assessed for the required simultaneous midpoint and extreme-label constraints, so worldwide priority of the complete statement remains unknown.

Earlier sources: [Luiz–Campos–Richter, Lemma 4 and Theorem 14](https://ic.unicamp.br/~reltech/2017/17-12.pdf); [Cattell, *Graceful labellings of paths*](https://www.sciencedirect.com/science/article/pii/S0012365X07001215). The first source also restates the earlier path and amalgamation ingredients.

AI tools assisted construction and proof development, coding, Lean formalization, certificate checks and source comparison. The separate internal replay compiled all 27 Lean modules and rejected five semantic negative controls. These project checks are not external scholarly review.
