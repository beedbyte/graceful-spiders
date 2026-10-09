# Editorial and scope audit — graceful growing-depth candidate
Date: 2026-10-09  
Candidate: gd-2026-10-09-rc1 (private/HOLD)

## Review basis

Compared text-en.md, text-de.md, and text-zh.md in the private candidate folder with the frozen statement in research-audits/graceful-whole-arm-next-2026-10-09/proof.md. The frozen proof states a path α-labeling and then, by known composition/complementation, separate graceful labelings for the spider at depths 4s and 4s+1. This was a wording and scope review only; it is not a second proof or a literature review.

The live site and source use “grazile Beschriftung” for graceful labeling and “α-Beschriftung” for alpha-labeling (for example, the published three-arm spider note). The candidate’s German “Alpha-Markierung” and “graceful Markierung” should be aligned with those terms.

## Recommended German terminology edits

Apply consistently throughout text-de.md:

- Alpha-Markierung → α-Beschriftung
- Mittelpunktmarkierung → Mittelpunktbeschriftung
- Endpunktmarkierungen → Endpunktbeschriftungen
- graceful Markierung → grazile Beschriftung
- Alpha-Markierung für jede Nullposition → α-Beschriftung mit Null an jeder vorgegebenen Position

“α-Amalgamation” can remain as the name of the established composition ingredient; in prose, “die bekannte α-Amalgamation” is smoother than “Bekannte Alpha-Amalgamation.” Keep “Komplementierung” if that is the project’s chosen term for the operation.

## Proposed German abstract

> Wir geben eine explizite Konstruktion für eine mit der Armlänge wachsende Menge vorgegebener Nullpositionen in Spinnengraphen mit gleich langen Armen an. Seien s ≥ 1 und r ≥ 3s ganze Zahlen mit r ≠ 3s + 1, und sei k = 2r + 1. Die Konstruktion liefert eine α-Beschriftung des Pfades P_(2k+1) mit der Mittelpunktbeschriftung k − 1 und der Schwelle k − 1, mit der Null in Tiefe 4s und mit dem Maximum 2k in der benachbarten Tiefe 4s + 1 desselben Arms. Die Endpunkte tragen die Beschriftungen (3k − 1)/2 und (3k + 1)/2. Mit der bekannten α-Amalgamation und einer Komplementierung erhält man für jedes n ≥ 2 und m ≥ 0 eine grazile Beschriftung von S(k^n,1^m), bei der ein beliebig vorgegebener Knoten eines langen Arms in Tiefe 4s oder 4s + 1 die Null trägt. Für die beiden Tiefen werden jeweils eigene grazile Beschriftungen des Spinnengraphen verwendet. Für jedes ungerade k ≥ 11 sind mindestens 2 floor((k − 5)/6) verschiedene Tiefen abgedeckt. Dies ist eine partielle Abdeckung vorgegebener Nullpositionen; die mathematische Priorität ist ungeklärt.

## Version note: replace the process-heavy paragraph

The proposed note is too long for a public change log. It mixes the mathematical change with finite-check counts, corruption tests, review gates, package internals, and candidate hold status. Those details belong in the private audit or evidence section. Do not publish “The candidate remains HOLD …” as a version note; HOLD is internal release status. Keep the version note focused on what this release adds and the result’s boundary.

Suggested English:

> Adds a construction for prescribed zeros at long-arm depths 4s and 4s + 1 in S(k^n,1^m), where k = 2r + 1, s ≥ 1, r ≥ 3s, r ≠ 3s + 1, n ≥ 2, and m ≥ 0. The number of guaranteed depths grows with k; this is not a full zero-rotatability result. The two zero positions use separate spider labelings.

Suggested German:

> Ergänzt eine Konstruktion für vorgegebene Nullpositionen in den Tiefen 4s und 4s + 1 an langen Armen von S(k^n,1^m), wobei k = 2r + 1, s ≥ 1, r ≥ 3s, r ≠ 3s + 1, n ≥ 2 und m ≥ 0 gilt. Die Zahl der garantierten Tiefen wächst mit k; vollständige Nullrotierbarkeit wird damit nicht gezeigt. Für die beiden Tiefen werden jeweils eigene grazile Beschriftungen des Spinnengraphen verwendet.

Suggested Chinese:

> 新增一种构造：对于满足 k = 2r + 1、s ≥ 1、r ≥ 3s、r ≠ 3s + 1、n ≥ 2、m ≥ 0 的 S(k^n,1^m)，可在长臂深度 4s 和 4s + 1 的指定顶点处实现零标号。保证覆盖的深度数量随 k 增长；这并未证明完全零可旋转性。两个指定零位置分别由不同的优美标号实现。

These notes deliberately omit finite artifact counts and the unresolved-priority caveat to stay readable as a changelog. That does not remove those points from the candidate’s detailed contribution and evidence text.

## Scope and translation risks

- Preserve the distinction between the path result and the spider result: the constructed path has an α-labeling; composition yields graceful spider labelings. Do not call the spider labeling an α-labeling.
- State that depth 4s and depth 4s+1 are realized by separate spider labelings. The single path α-labeling has both zero and maximum at adjacent depths; avoid making that sound like one spider labeling covers both.
- Retain s ≥ 1, r ≥ 3s, r ≠ 3s+1, k = 2r+1, n ≥ 2, and m ≥ 0. The excluded parameter relation is a limitation of this formula, not a nonexistence result.
- Keep the uniform count explicitly as a lower bound for odd k ≥ 11. At k = 6t + 1, s = t is an additional case beyond that uniform bound.
- “Alpha-Markierung” is a terminology issue, not a mathematical change. “Graceful Markierung” is an unnecessary English/German hybrid; “grazile Beschriftung” matches established site wording.
- The Chinese uses α 标号 for alpha-labeling and 优美标号 for graceful labeling, which preserves the path/spider distinction. Keep this consistent in later copy.
- Keep the prior-work statements provisional. The frozen proof explicitly says Cattell and related older machinery have not been fully compared; do not strengthen this into a novelty, priority, or non-subsumption claim.
- The finite counts (156 paths and 960 spider labelings) describe transcription checks only. If retained in detailed evidence, state they do not replace the all-parameter proof, as the candidate already does.

## Disposition

Recommend revising the German terminology and midpoint-label phrasing before language review. Replace the proposed version note with the concise three-language versions above. No mathematical scope change is required by these edits. The candidate remains private until its separate mathematical/source review and contribution review are complete.

