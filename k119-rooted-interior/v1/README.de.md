# Nullwerte im gesamten Innenbereich eines gewurzelten Verbunds mit 119-Kanten-Armen

**Beedbyte · Quellenpaket v1**

Jordi Gartner veröffentlicht diese Arbeit über Beedbyte. Deutsch ist ein Übersetzungsentwurf ohne dokumentierte menschliche Sprachprüfung.

## Satz für festes K119

Sei `H` ein beliebiger endlicher indizierter Graph mit `Q` Kanten. Es sei eine konventionell graziöse Beschriftung `g` sowie eine angegebene Wurzel `r` mit `g(r)=0` vorgegeben. Zwei neue Arme der Länge 119 werden angefügt, indem ihr gemeinsamer Pfadmittelpunkt – Index 119 eines Pfades mit 238 Kanten – mit `r` identifiziert wird. Für jede ganzzahlige Tiefe `d` mit `1≤d≤118` kann jeder der beiden benannten Armknoten an den Pfadindizes `119−d` und `119+d` in einer konventionell graziösen Beschriftung des gesamten Verbunds den Wert 0 erhalten. Jedes Ziel hat eine eigene Beschriftung. Die Kantenbeschriftung reicht bis `238+Q`.

Die vorgegebene Wurzelbeschriftung mit Wert 0 ist eine Voraussetzung. `H` muss weder zusammenhängend, azyklisch, ein Baum, onto-beschriftet noch alpha-beschriftet sein; auch `Q=0` ist zulässig. Die Aussage umfasst weder die gemeinsame Wurzel noch alte Knoten von `H`, die neuen Spitzen bei Tiefe 119 oder zwei Ziele gleichzeitig.

## All-r-Familien nahe den Spitzen

Für jedes `r≥1` sei `K_r=30·4^r−1`. Der kopierte Quellabschluss beweist getrennte Nullbeschriftungen auf jedem benannten neuen `K_r`-Kanten-Arm an den folgenden vier Tiefenpaaren, jeweils für beliebiges vorgegebenes konventionell graziös beschriftetes endliches `H` mit Wurzelwert 0:

| Quellsatz | Tiefen |
|---|---|
| `TerminalNormalized.rooted_both` | `K_r−8`, `K_r−7` |
| `TerminalSeed56.rooted_both` | `K_r−6`, `K_r−5` |
| `TerminalSeed34.rooted_both` | `K_r−4`, `K_r−3` |
| `TerminalSeed12.rooted_both` | `K_r−2`, `K_r−1` |

Zusammen ergeben sie die acht Tiefen `K_r−8,…,K_r−1`, jeweils mit einer eigenen zielabhängigen Beschriftung. Dies ist eine Aussage nur für diese acht Positionen nahe der Spitze; sie beweist keine vollständige Innenabdeckung für `r>1` oder für jede ungerade Armlänge. Der feste Satz `K119Through118.expanded` behandelt separat alle inneren Tiefen 1–118 für `K=119`.

## Beweisaufbau und frühere Arbeiten

Der feste Satz verbindet das eingefrorene Ergebnis `K119Through114.interior` für die Tiefen 1–114 mit den zwei terminalen Seed-Familien für 115–116 und 117–118. Die ältere Abdeckung 1–114 bleibt unverändert in `source/K119Through114.lean` erhalten. Die beiden neuen Seedwörter mit je 59 Einträgen und ihre korrigierten Quellenbindungen liegen unter `evidence/`; ältere Eingabedatensätze wurden nicht geändert.

Die Erweiterung terminal-normalisierter Pfade verwendet eine ältere, an Endpunkten angepasste Verkettung graziöser Permutationen und beansprucht keine neue Verkettungsoperation. Ihre veröffentlichte Vorgeschichte umfasst die Konstruktion im Beweis von [Hicks–Ollis–Schmitt, Lemma 4.5](https://community.middlebury.edu/~jschmitt/papers/HicksOllisSchmitt2018.pdf) sowie [Adamaszek, Lemma 1](https://arxiv.org/pdf/math/0608513). Auch die allgemeine Alpha-Verklebung mit einer Wurzel vom Wert 0 ist frühere Arbeit; sie wird in [Panpa, Imnang und Wasuanankul (2025), Satz 2.5](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777) und [Shan–Zhong (2026), Lemma 1](https://arxiv.org/html/2605.14295v2) formuliert. Zweimalige Anwendung von [Shan–Zhong, Satz 2](https://arxiv.org/html/2605.14295v2) ergibt bereits die Fälle für beliebiges `H` in Tiefe 1 und 2 auf jedem der beiden benannten Arme; [Luiz–Campos–Richter (2017), Satz 14](https://ic.unicamp.br/~reltech/2017/17-12.pdf) behandelt den Fall eines zentralen Blatts. Die älteren Operationen und diese Spezialfälle werden anerkannt. Ob frühere Ergebnisse den gesamten K119-Bereich 1–118 implizieren, ist ungeklärt; die weltweite Priorität ist **UNKNOWN**.

## Reproduktion und Prüfung

Das Paket enthält alle 68 Lean-Module im transitiven Quellabschluss, die exakte Modulreihenfolge und 19 Kontrollmodule: 3 positive Prüfungen und 16 negative Kontrollen. `build.py` erhält den Lean-Programmdateipfad und ein neues Ausgabeverzeichnis außerhalb des Pakets als Argumente. Es prüft die SHA256-Prüfsumme von Lean 4.34.0, die Paketquellen und Kontrollen, kompiliert in frische Objekte mit Warnungen als Fehlern und führt anschließend `Support`, `Positive`, `WholeClosure` sowie 16 semantische Mutanten aus. `check_path_guard.py` prüft Ausgabepfade und vorhandene bzw. defekte Symlinks; `verify_package.py` kontrolliert die Dateiintegrität. Diese Python-Skripte sollten mit `python -B` ausgeführt werden, damit keine Bytecode-Dateien entstehen. Netzwerkzugriff oder ein weiterer Projekt-Checkout sind nicht erforderlich.

Der Autorenbuild kompilierte alle 68 Quellen und zählte 2.809 Theoremabschlüsse, deren Axiome ausschließlich `propext`, `Classical.choice` und `Quot.sound` sind. Eine getrennte Prüfung aus kopierten Quellen kompilierte alle 68 Module erneut, prüfte fünf zentrale Theoremsätze und verwarf acht semantisch falsche Kontrollen. Die Autorenkontrollen umfassen außerdem 1.072 konkrete Fälle und 16 wirksame semantische Mutanten. Dies sind projektinterne Prüfungen, keine externe Begutachtung oder Peer-Review. Zur formalen Vertrauensbasis gehören Lean-Kernel, Compiler, Standardbibliothek und die kodierten Graphdefinitionen. Die eingefrorenen Autoren- und Replay-Berichte sind unter `evidence/` enthalten.

## Methoden und Beiträge

KI-Werkzeuge unterstützten die dokumentierte Lean-Implementierung und Reproduktions-/Prüfscripte sowie die Erstellung der deutschen und chinesischen Übersetzungsentwürfe. Formalbeweis und Prüfung aus kopierten Quellen sind getrennte projektinterne Artefakte; keines davon ist eine externe Begutachtung.

Version 1 ergänzt einen formalen Beweis für getrennte Nullbeschriftungen auf allen inneren Tiefen 1–118 bei K119 und führt die all-r-Tiefenpaare `K_r−8,…,K_r−1` auf.
