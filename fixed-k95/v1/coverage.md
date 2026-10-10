# Complete target map / Vollständige Zielzuordnung / 完整目标对应

All rows apply to actual `S(95^n,1^m)`, every `n≥2,m≥0`, and a separately selected actual vertex. Physical arm depth d means the zero-based Lean index d−1. Short-leaf targets exist only when m>0. The exact per-depth certificates are in [data/lean-catalog.json](data/lean-catalog.json); this table groups those94 interior rows.

| Actual target / tatsächliches Ziel / 实际目标 | Source route |
|---|---|
| Hub / Hub / 中心 | `K95Boundary.center_zero`: explicit root-zero residual |
| Each short leaf / jedes Kurzblatt / 每个短叶 | `K95Boundary.leaf_zero`: whole-graph complement and leaf permutation |
| Depth1 | Explicit midpoint-alpha P191 word |
| Depths2..71 | Compatible cores at p46 and H3 shell |
| Depths72/73 | p19 delta3 seed, q9 insertions, reflection, H3 shell |
| Depths74..77 | p37/q9 P4/P2 source words; retained overlap at77 |
| Depths78..86 | t3 q24 words from both starting windows; family coverage also includes77 |
| Depths87..92 | Six separately pinned P191 literals, including overlapping extrema |
| Depths93/94 | H1 seed23 with explicit C72 append |
| Tip95 / Spitze95 / 端点95 | `K95Tip.tips_prescribed_zero`: direct physical endpoint extension |

`K95Full.interior` uses51 distinct literal words for depths1..94. The catalog contains each191-label word, zero/maximal depth, selected component, origin and certificate number. The maximum-derived component uses complement on the entire spider. The principal wrapper case-splits hub, original leaf and named arm vertex; it does not infer a graph theorem merely from a numerical range union.

The separate aggregate mathematical catalog is preserved as [evidence/math-catalog.json](evidence/math-catalog.json). It independently covers the same targets; its72/73 source is an alternative to the Lean author's source. The two catalogs are not claimed byte-identical. Author formal coverage uses the exact Lean catalog above.

The old D8 bound at k95 is73, whereas an earlier Compatible formula gives71. The specific72/73 words close that distinction. This package verifies those fixed witnesses, not a replacement formula inferred from finite tests.

Status: mathematical aggregate GO, Lean author GO, separate copied-source replay GO. This is a fixed-k95 result, not a theorem for all odd lengths. Literature priority is UNKNOWN.
