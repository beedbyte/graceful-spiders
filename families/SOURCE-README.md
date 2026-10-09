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

## Editorially reviewed manuscript copies

`notes/article.en.md`, `notes/article.de.md`, and `notes/article.zh.md` are repository-readable copies of the frozen public manuscripts. Only link destinations were adapted to adjacent files. Original prose, mathematical content, code blocks, link labels, and line endings are retained. `notes/MANIFEST.json` records the exact approved source hashes, output hashes, and URL substitutions. CMS templates remain separate and obtain their commit/download destinations during publication.

The standalone proof ZIP remains the proof-only snapshot prepared at commit `04c131d0b621b32f3c471c9e6b82b25ddbaac19f`, SHA-256 `bb46e42b048de2d3bc4156ab68bf05eca17f18491c3b84e87c5fc92a5d1c98e6`. It excludes these three manuscript copies and subsequent repository documentation changes. Its own included hash list describes that snapshot. The repository's updated `SHA256SUMS.txt` describes the current `families/` tree. These are distinct, explicitly identified integrity scopes.

## Independently audited eleven-edge extension

`k11/` adds four exact alpha-path certificates covering depth pairs (2,3), (4,5), (6,7), (8,9). Together with the unchanged base proof this proves the union `k in {3,5,7,9,11}`, `n>=2`, `m>=0`. K11 underwent a separate agent mathematical audit and independent implementation; publication priority is unresolved. `SOURCE-MANIFEST.json` records original source hashes and every packaging adaptation. Existing 3/5/7/9 proof/certificate/checker bytes and the earlier three manuscript copies are unchanged.

The new `graceful-family-k11-public-proof.zip` contains the current proof-only files under `families/`, excluding `families/notes/`. Its hash list covers only its actual archive members. The repository's hash list additionally covers manuscript copies. The earlier ZIP/hash recorded above remains a historical snapshot and is retained unchanged.

The public K11 independent checker, audit and generated report are under `k11/independent/`, matching the manuscript references. The checker resolves certificates/source files in its parent `k11/` directory and the unchanged base proof in `families/`. Only filesystem resolution and hash-report paths changed; mathematical checking code is unchanged.

## Combined five-length manuscript update

The three `notes/` copies now use the exact separately approved five-length PUBLIC templates. `notes/MANIFEST.json` records all source/output hashes and URL substitutions. The Chinese deployment-only placeholder annotation was removed during repository link resolution; its exact original line hash and text with token names are recorded. Mathematical prose, all ten certificate rows, commands, and remaining article bytes are unchanged. Earlier manuscript-copy entries above describe their historical snapshot.

Repository articles use relative source links and the reproduction guide. The CMS release must insert the actual final repository commit and actual uploaded asset ID into separate CMS copies after those identifiers exist. No tracked article embeds its own commit hash. The combined proof ZIP remains the verified source snapshot at `a005347d2f0b0d56fc6950647fb13fa4ce96e30d`, SHA-256 `83e82afab5988ebb3cd3d19d9cc08d7945cf6bde5257b415f4ae662fd220be32`, with `families/` and without `notes/`.
