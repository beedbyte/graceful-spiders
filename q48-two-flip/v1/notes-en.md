# Beedbyte — q48 two-flip family

Version q48-two-flip-v1. Reader-note language draft; no human language review is recorded. Jordi Gartner publishes this work through Beedbyte.

For every integer **t>=2**, put **k=23+24t**. For all **n>=2,m>=0**, every selected named long arm of **S(k^n,1^m)** has a separate graceful labeling with zero at each of the physical depths **21+22t** and **22+22t**. Labels are0..nk+m and absolute edge differences1..nk+m. Every original short leaf remains in the graph; different requested zeros use different labelings.

The construction uses t-2 stationary q24 steps followed by one terminal q48 macro. Its output has changed neighbors and cannot be iterated through the unchanged old contract. This is not a full zero-rotatability statement for all vertices of this progression.

All36 Lean sources were replayed from fresh source copies with warnings as errors. All1992 theorem closures use only standard axioms;11 Lean mutants and22 mathematical mutants were rejected. The unbounded quantifiers come from symbolic proofs and Lean, not finite tests. The exact principal is `GracefulBoundary.Q48Flip.selected_actual`.

Earlier concatenation and insertion operations on graceful path permutations are credited in [REFERENCES.md](REFERENCES.md). The graph transfer is proved in INVENTORY.md and Lean; those path citations are not a historical attribution for the graph-level transfer. Worldwide priority is **UNKNOWN**. AI tools assisted construction, proof/code, separate internal checks, and translation. These checks are internal project checks, not external review or peer review. No license grant is included. See [README.md](README.md) for evidence and reproduction.
