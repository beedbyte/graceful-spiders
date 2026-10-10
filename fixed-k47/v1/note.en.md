# Zero-rotatability for spiders with 47-edge arms

Jordi Gartner publishes this work through Beedbyte.

Let `S(47^n,1^m)` be the tree with a center, `n` separately named arms of 47 edges each, and `m` separately named original leaves adjacent to the center. For every `n ≥ 2` and `m ≥ 0`, each actual vertex—the center, every depth from 1 through 47 on each named arm, and each of the `m` leaves that exists—can receive label zero in a graceful labeling. The labeling may depend on the selected vertex. The graph has `N=47n+m` edges; a graceful labeling bijects its vertices with `0,…,N` and its edge differences with `1,…,N`.

The construction uses finite 95-vertex alpha-path certificates for arm depths 1–38, a mixed q24 construction for depths 39–42, a q30 construction for depths 43–44, a direct path certificate for depth 45, and a tip construction for depths 46–47. Separate root-zero constructions handle the center and each original center leaf. The source covers the fixed arm length 47; it does not prove a result for every odd arm length or an unbounded q24/q30 progression.

The complete path cases `n=2,m=0` and `n=2,m=1` have prior coverage in Luiz, Campos, and Richter’s [*Some families of 0-rotatable graceful caterpillars* (2017), report IC-17-12](https://ic.unicamp.br/~reltech/2017/17-12.pdf); the latter is a path with one leaf attached at its center. Root-zero spiders, alpha-amalgamation, graph complementation, and ordinary gracefulness results for equal-arm spiders are also prior tools. [Patterson’s 2017 thesis](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content) discusses related attachments and states a broad spider zero-rotatability conjecture. A bounded comparison does not determine whether earlier path constructions supply the joint source conditions used here; the full historical priority therefore remains **UNKNOWN**. See also Cattell, [*Graceful labellings of paths* (2007)](https://doi.org/10.1016/j.disc.2007.03.046), and Bahls, Lake, and Wertheim, [*Gracefulness of families of spiders* (2010)](https://msp.org/involve/2010/3-3/involve-v3-n3-p01-s.pdf).

The Lean declarations `GracefulBoundary.K47Full.all_vertices` and `GracefulBoundary.K47Full.all_vertices_unique_zero` formalize the universal actual-vertex statement and its unique-zero refinement. The reproducible package contains 42 byte-pinned Lean modules. A separate copied-source replay compiled all 42 with warnings treated as errors, checked 2,201 theorem closures including 111 private declarations against the standard Lean axioms, checked 191 actual named vertices for `n=2,m=0/1`, and rejected six semantic negative controls. These are internal project checks, not external review or peer review.

## Methods

AI tools materially assisted development of the source constructions, checker code, mathematical synthesis, and parts of the literature comparison, and preparation of draft German and Chinese translations. The Lean build and separate checks are internal project verification; they are not external scholarly review. Jordi Gartner retains publication responsibility through Beedbyte.

No PDF is supplied with this source package.
