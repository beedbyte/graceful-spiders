# Null-Rotierbarkeit von Spidern mit Armen aus 95 Kanten

**Beedbyte — Quellenpaket v1**

Jordi Gartner veröffentlicht diese Arbeit über Beedbyte. [English](README.md) · [简体中文](README.zh-CN.md)

## Satz

Für alle ganzen Zahlen `n ≥ 2`, `m ≥ 0` und jeden tatsächlich vorhandenen Knoten v von `S(95^n,1^m)` existiert eine graceful Beschriftung mit Null an v. Der Graph hat einen Hub, n benannte Arme mit jeweils genau 95 Kanten und m ursprüngliche Kurzblätter am Hub. Für jedes Ziel wird eine eigene Beschriftung verwendet; die Knotenlabels sind genau `0,…,95n+m`, die Kantendifferenzen genau `1,…,95n+m`. Erfasst sind der Hub, alle benannten Arme in den physischen Tiefen 1..95 und jedes vorhandene Kurzblatt. Bei m=0 gibt es kein Kurzblattziel. Ein Satz für andere ungerade Armlängen wird nicht behauptet.

Der Lean-Einstiegssatz heißt `GracefulBoundary.K95Full.all_vertices`; `unique_zero` kennzeichnet den gewählten Knoten zusätzlich als einzigen Nullort. Siehe [K95Full.lean](source/K95Full.lean), die [vollständige Tiefenzuordnung](coverage.md) und den [exakten Katalog](data/lean-catalog.json).

## Beweis und Prüfung

Einundfünfzig Mittelpunkt-Alpha-Wörter für P191 decken die Armtiefen1..94 ab. Lean prüft die vollständigen Label-/Differenzinventare, den Schnitt 94, den physischen Mittelpunktindex 95 mit Label 94 sowie die ausgewählten Extremwerte. Eine bekannte Alpha-Amalgamation mit explizitem, an der Wurzel mit Null beschriftetem Restbaum überträgt jedes Wort auf alle n,m und jeden benannten Arm. Für Maximum-Ziele wird der gesamte Graph komplementiert. Explizite Konstruktionen behandeln Hub, ursprüngliche Kurzblätter und die tatsächliche Spitze 95.

Status: **separate interne mathematische QA GO; Lean-Autorbuild GO; separater Copied-Source-Lean-Replay GO.** Der Autorbuild kompilierte 35 Quellmodule mit Lean 4.34.0 und Warnungen als Fehlern; geprüft wurden 1678 Theorem-Axiomabschlüsse mit ausschließlich Standardaxiomen, 671 benannte Beispiele und 12 semantische Negativkontrollen. Der spätere [separate Replay](evidence/separate-lean-replay.md) baute alle 35 Module neu und prüfte acht benannte Theorem-Abschlüsse, 13 Beispiele und acht semantische Kontrollen. Die mathematische Gesamtprüfung verwendet eine eigene Implementierung und einen universellen Transferbeweis. Diese Prüfungen sind intern, keine externe Begutachtung oder Peer Review.

Dieses Paket enthält ausschließlich Quellen, keine kompilierten Objekte. Zur Vertrauensgrenze gehören Lean-Kernel/-Programm und Standardbibliothek sowie Graphdefinitionen und ihre mathematische Interpretation. Ausgewählte eingefrorene Berichte und Originalmanifeste stehen unter [evidence](evidence/); diese Manifeste beschreiben ihre ursprünglichen Auditverzeichnisse, nicht das Inventar dieses Pakets. Die Evidenzberichte geben den Status zum jeweiligen Einfrierdatum wieder; der obige aktuelle Prüfstand berücksichtigt spätere Nachweise. Kopierherkunft und Prüfsummen stehen in [provenance.json](provenance.json).

## Vorarbeiten und Grenzen

Ältere Alpha-Amalgamation, Permutationseinfügung und Verkettung werden ausdrücklich anerkannt, darunter [Hicks–Ollis–Schmitt, Beweis zu Lemma4.5](https://community.middlebury.edu/~jschmitt/papers/HicksOllisSchmitt2018.pdf), [Adamaszek, Lemma1](https://arxiv.org/pdf/math/0608513) und [Ollis, Lemma5.5/Theorem5.6](https://ajc.maths.uq.edu.au/pdf/78/ajc_v78_p035.pdf). Der H1-Zweig verwendet eine ältere Verkettungsoperation. [Luiz–Campos–Richter, Lemma4/Theorem14](https://ic.unicamp.br/~reltech/2017/17-12.pdf) deckt bereits jeden Knoten der Teilfamilien `n=2,m=0/1` ab. Lemma5 betrifft gewöhnliche graceful Freiheit an einem vorgeschriebenen Punkt, keine gemeinsame Mittelpunkt-/Alpha-/Extremwertbedingung.

Die weltweite Priorität bleibt **UNKNOWN**. Der [begrenzte Vergleich](evidence/bounded-priority.md) dokumentiert weitere Überschneidungen und die offene Volltextlücke bei [Cattell2007](https://doi.org/10.1016/j.disc.2007.03.046). Weder fehlender Zugriff noch ein neuer Projektkatalog belegen Neuheit.

## Reproduktion und Beiträge

Benötigt werden Python 3.10+ und Lean 4.34.0; kein Solver:

```
python build.py --check
python verify_catalog.py
python -O verify_catalog.py
python build.py --lean /path/to/lean --output /new/directory/outside/this/package
```

Der Builder prüft alle Paketprüfsummen in SHA256SUMS.txt, kompiliert in Abhängigkeitsreihenfolge und setzt LEAN_PATH ausschließlich auf sein frisches Ausgabeverzeichnis. KI-Werkzeuge unterstützten die dokumentierte Quellenkonstruktion, Beweisentwicklung, Programmierung, Lean-Formalisierung, Literaturprüfung und internen Gegenprüfungen. Diese Beiträge sind von Jordi Gartners Veröffentlichungsverantwortung zu unterscheiden. Die übersetzten Leserhinweise wurden intern auf Konsistenz geprüft; eine externe Sprachprüfung ist nicht dokumentiert.

Version 1 enthält den festen k95-Satz, den vollständigen Katalog innerer Tiefen, Rand-/Spitzenquellen, Reproduktionswerkzeuge und ausgewählte Belege.
