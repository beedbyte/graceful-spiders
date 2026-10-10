# Beedbyte — two 95-edge arms over a rooted graceful graph

This English note is the original; the German and Simplified Chinese versions are translation drafts. Jordi Gartner owns this work and publishes it through Beedbyte.

## Exact result

Let H be any finite indexed graph with Q edges, a specified vertex r, and a supplied conventional graceful labeling g. This means that vertex labels are injective in 0..Q and edge absolute differences are bijective onto 1..Q. Require g(r)=0.

Identify r with the midpoint of a new 190-edge path, adding two separately named 95-edge arms and retaining every old H vertex and edge. For either new arm and each physical depth d=1..94, the resulting graph has a target-dependent conventional graceful labeling with zero at that actual selected new vertex. Each arm/depth request may use a different labeling. Output labels are injective in 0..Q+190 and edge weights are exactly 1..Q+190.

H need not be a tree, connected, alpha-labeled or onto-labeled. The non-onto triangle labeled 0,1,3 is included. The theorem requires the supplied zero labeling at the chosen root; it does not establish that an arbitrary specified root admits such a labeling. It makes no claim for the new tips at depth 95, old H target vertices, or the stronger onto-vertex predicate.

The exact Lean declaration is `GracefulBoundary.K95Rooted.interior` in [source/K95Rooted.lean](source/K95Rooted.lean). Its conjunction supplies separate witnesses for the actual graft vertices at path indices 95-d and 95+d.

## Evidence and methods

The packet includes the mathematical author proof, a separately implemented internal mathematical check, the Lean author report, and a separate internal copied-source replay. The mathematical check disclosed limited exposure to author prose and is not described as fully blind. It did not use the author's checker.

The copied-source replay rebuilt all 59 transitive project modules from an empty object directory with Lean 4.34.0 and warnings as errors. It checked 2,239 module-origin theorem axiom closures, all using only the standard axioms `propext`, `Classical.choice`, `Quot.sound`; the exact theorem type; the non-onto triangle at all 94 depths on both arms; 196 concrete target assertions; and four effective root/tip/old-vertex/onto controls. No author or predecessor objects were imported. The compiler and its standard library are the stated trust boundary; the standard library was not rebuilt. These are internal project checks, not external scholarly peer review.

AI tools assisted the documented construction and proof-code work, literal and graph checking, separately tasked internal source replay, and these reader-note translations. Publishing responsibility remains with Jordi Gartner through Beedbyte. Exact artifact hashes and the review boundaries are in [evidence-pins.json](evidence-pins.json) and the preserved evidence reports.

The high-side d-graceful shift, translations, complement and vertex amalgamation are established operations. The general alpha-vertex amalgamation of an alpha-labeled graph with a graceful graph labeled 0 at the identified vertex is stated by Panpa, Imnang and Wasuanankul (2025, Theorem 2.5, recalling Huang–Kotzig–Rosa) and by Shan and Zhong (2026, Lemma 1). The present construction uses this operation with the graceful rooted graph H and an alpha-labeled path. Barrientos (2020), *Alpha graphs with different pendent paths*, printed pp. 302–303, describes the component transformations and a narrower amalgamation with two alpha-graph inputs; see the [publisher PDF](https://www.ejgta.org/index.php/ejgta/article/download/1036/pdf_143). That is operation overlap, not a verbatim theorem for arbitrary H. No new primitive operation is claimed. Priority of the exact positional graph-family result is **UNKNOWN**; no exhaustive worldwide comparison or external review is asserted. See [Panpa–Imnang–Wasuanankul, Theorem 2.5](https://onlinelibrary.wiley.com/doi/10.1155/jama/5826777) and [Shan–Zhong, Lemma 1](https://arxiv.org/html/2605.14295v2).

## Reproduce

The package contains the complete 59-source project import closure, independent checks, module order and source/evidence inventories. Proof-source bytes equal the frozen replay inputs. Run Python 3 with the exactly verified Windows Lean executable and a new or empty build directory:

```text
python -B build.py --lean "path/to/lean.exe" --build-dir "new-empty-build-folder"
```

The executable must match SHA256 `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2` (Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`). This reproducer does not install software or certify a different compiler/platform. It verifies the package inventory, builds fresh objects, repeats the type/triangle/axiom checks, and expects the four semantic mutants to fail. It deletes nothing. `SHA256SUMS.txt` inventories all package payloads except its own exact root path.

German: [README.de.md](README.de.md). Simplified Chinese: [README.zh-CN.md](README.zh-CN.md). All three notes retain the same theorem scope and verification limits.
