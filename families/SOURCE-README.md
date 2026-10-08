# Source and packaging provenance

The source snapshots were prepared on 9 October 2026. `SOURCE-MANIFEST.json` records the original SHA-256 values under relative provenance names; those names identify research records, not paths required to run this package. The historical raw audit reports remain in the research records and are not included as public raw copies.

Packaging changes:

- `construct.py`, `verify.py`, and `certificates.json` are byte-identical to their audited sources.
- `proof.md` retains the theorem, mathematical Sections 1–6, certificate tables, evidence limits, and next mathematical question. Its status introduction records the completed separate agent audit; its reproduction section now gives the two portable checks and omits exploratory search instructions. No mathematical argument was changed.
- `literature.md` replaces a private extraction path with a description and omits a historical external-write status line.
- `independent/verify_independent.py` changes only `SOURCE` to resolve the adjacent package. Its independently implemented construction and graph checks are unchanged.
- `independent/AUDIT.md` and `LITERATURE-AUDIT.md` are explicitly disclosed public adaptations, not raw reports. Local paths and historical workflow status were omitted or adapted; substantive arguments and literature limits remain. Fresh verification results replace historical package hashes.
- Search utilities, search histories, caches, and private work records are excluded. The proof requires the six included certificates, not a search run.

Both checkers were rerun after packaging and after extracting a temporary ZIP into a fresh directory. `REPRODUCIBILITY.md` records the counts and extraction instructions; `SHA256SUMS.txt` records package-file hashes. Earlier `notes/`, `proof/`, and `k7/` were verified byte-for-byte unchanged against the pre-packaging baseline.
