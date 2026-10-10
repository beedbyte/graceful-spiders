# Zero-rotatability for fixed 25-edge arm spiders

Jordi Gartner publishes this work through Beedbyte.

Let `S(25^n,1^m)` be the tree with a center, `n` separately named arms of 25 edges each, and `m` original, separately named leaves at the center. For every `n ≥ 2` and `m ≥ 0`, every actual vertex can receive label zero in a graceful labeling. The chosen vertex determines the labeling; this is not a claim that one labeling has zero at all vertices. The quantified vertices are the center, all 25 vertices on each named arm, and exactly the `m` leaves that exist.

The Lean declarations `K25Full.all_vertices` and `K25Full.all_vertices_unique_zero` formalize the existence and unique-zero forms for the actual graph. The construction combines finite alpha-path certificates with the residual-spider transfer, explicit center and leaf constructions, and a fixed-25 tip construction. It proves arm length 25 only. It does not prove a theorem for every odd arm length or the unbounded F20/F18 progressions.

The cases `n=2,m=0` and `n=2,m=1` have prior path-family coverage: the first is `P51`, and the second is `P51` with a leaf attached at its center, as in Theorem 14 of Luiz, Campos and Richter, [“Some families of 0-rotatable graceful caterpillars” (2017)](https://ic.unicamp.br/~reltech/2017/17-12.pdf). This overlap does not determine whether the full all-`n,m` theorem was previously stated or follows elsewhere. Worldwide priority is **UNKNOWN**.

The source package contains 27 Lean modules and a reproducible isolated build. A separate internal copied-source replay rebuilt all modules with warnings treated as errors, audited theorem closures against the standard Lean axioms, checked every actual named vertex for `n=2,m=0/1`, and rejected five semantic negative controls. Internal checks are not external scholarly review or peer review. AI tools assisted proof and construction development, code and Lean formalization, certificate checks, and source comparison.

No PDF is supplied with this source package.
