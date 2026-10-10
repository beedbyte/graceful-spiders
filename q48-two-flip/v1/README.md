# Beedbyte — q48 two-flip terminal family

Version `q48-two-flip-v1`, 10 October 2026. Jordi Gartner publishes this work through Beedbyte.

For every integer **t>=2**, let **k=23+24t**. For every **n>=2,m>=0** and every selected named long arm of the actual spider **S(k^n,1^m)**, there is a separate graceful labeling with zero at each of the two physical depths **21+22t** and **22+22t**. Each request uses its own labeling. All original short leaves are retained.

The construction is terminal: perform t-2 old stationary q24 steps, then one q48 macro representing two different zero-order flips. The resulting window is H13,L0,H0,L1. It does not satisfy the original H1,L0,H0,L2 recurrence contract, so further iteration of that interface is not justified. No full zero-rotatability theorem for this entire odd-length progression is claimed here.

The Lean principal is `GracefulBoundary.Q48Flip.selected_actual` in [Q48Family.lean](source/Q48Family.lean). It quantifies over the actual `SpiderVertex` graph, every `a : Fin n`, and either specified depth. Its premises contain no unproved source or residual assumption. Physical depth d is represented by the zero-based arm index d-1.

## Contents and methods

- [Symbolic inventory and graph transfer](INVENTORY.md).
- [Reader notes: English](notes-en.md), [Deutsch](notes-de.md), [简体中文](notes-zh.md).
- [Prior constructions and attribution](REFERENCES.md).
- [Evidence bindings](evidence/bindings.json), complete [mathematical check output](evidence/math-results.json), [Lean checks](evidence/lean-results.json), and [axiom closures](evidence/axiom-closures.txt).
- 36 unchanged Lean sources; finite literal checks use kernel `decide`.

AI tools assisted the certificate construction, symbolic proof development, checker and Lean code, separate internal mathematical checks, copied-source replay, and these translations. These are internal project checks, not external review or peer review. Worldwide priority is **UNKNOWN**. The language notes are drafts; no human language review is recorded. REFERENCES.md credits earlier constructions of graceful path permutations. The separate transfer from a midpoint-alpha path to the actual spider is proved in INVENTORY.md and the Lean sources; the cited path passages are not presented as pinpoint references for that graph-level transfer. Its historical priority remains unassessed here.

## Reproduce

Use Python3.10 or newer and **Lean4.34.0** with its standard library. No Python packages, solver, Mathlib, network fetch or predecessor object files are required by these commands. Run from the package directory; choose a new output directory outside the package:

```text
python build.py --check
python check_math.py > ../q48-math-normal.json
python -O check_math.py > ../q48-math-optimized.json
python build.py --lean /path/to/lean --output ../q48-build
python check_lean.py --lean /path/to/lean --objects ../q48-build --output ../q48-checks
```

On Windows, provide the corresponding `lean.exe` path in quotes. Compare the two mathematical output files byte-for-byte; both should also match `evidence/math-results.json`. The build script verifies the full package hash inventory and topological imports before compiling. It refuses an existing output directory, sets `LEAN_PATH` exclusively to that new directory, clears `LEAN_SRC_PATH`, and uses `-DwarningAsError=true` for all36 modules. It changes the compiler working directory to `source/` and passes **bare module filenames**. Preserve this invocation: Lean private declaration names can depend on source-path spelling.

The Lean check runner verifies that the generated objects belong to the exact package build before using them. It inspects all1992 project theorem closures, exercises42 named-arm examples plus6 other positive controls, and requires11 semantic mutants to fail. The mathematical runner checks100 full source words,120 named graphs,48,656 edges and22 effective mutants. Finite checks supplement the symbolic theorem and kernel proof; they are not an inference to unbounded parameters.

The exact checksum of `SHA256SUMS.txt` must be compared with a separately obtained release checksum; a checksum file alone is not an authenticity mechanism. The file inventories all package payloads except itself. Historical evidence digests identify the separate checks; reproducing the included tests does not require access to those historical records.

No license grant is included. No external-review or publication-priority status is implied by availability of these files. Source comments are retained verbatim to preserve the source hashes and may describe earlier development stages; the scoped current theorem and evidence boundary above govern this package.
