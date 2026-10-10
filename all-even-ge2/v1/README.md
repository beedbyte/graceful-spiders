# Zero-rotatability of equal even-arm spiders

Beedbyte. Jordi Gartner publishes this work through Beedbyte.

For every even arm length `k ≥ 2`, every `n ≥ 2`, every `m ≥ 0`, and every actual named vertex of `S(k^n,1^m)`, a graceful labeling can assign zero to that vertex. The labeling may depend on the selected vertex. The graph includes the center, `n` named arms of `k` edges, and `m` existing unit leaves.

## Read the result

- [English article](article.en.md) — editorial copy candidate.
- [Deutscher Artikel](article.de.md) — Übersetzungsentwurf; noch nicht sprachlich geprüft.
- [简体中文文章](article.zh.md) — 翻译草稿；尚未经人工语言审校。
- [Full English manuscript source](manuscript.tex) — LaTeX source; no verified PDF or rendered-layout review is available for this version.
- [Lean source and build instructions](lean/README.md) — 186 source modules, build order and SHA-256 index.

The three [version notes](version-note.en.md) are also available in [German](version-note.de.md) and [simplified Chinese](version-note.zh.md). They state the same theorem scope.

## Verification and limits

The Lean package was built from all 186 source modules with Lean 4.34.0 and warnings treated as errors. A separate internal source-package check queried theorem axiom dependencies, verified named graph boundary cases, and rejected altered statements. These are internal project checks, not external scholarly review. Reproduce the source build using [the packaged instructions](lean/README.md); the tested platform was Windows x86-64.

The manuscript source was checked mathematically and statically. Its PDF compilation failed before TeX analysis because the built-in compiler could not find standard directories, so PDF output and page layout remain unverified. The German and Chinese articles are draft translations without documented human language review. The cited literature supplies particular overlaps and construction tools; worldwide priority of the full theorem is unresolved. No reuse license is granted by this package; rights are reserved.

AI tools assisted the documented construction and proof development, coding, certificate checks and source inspection.
