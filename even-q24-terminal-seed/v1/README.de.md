# Ein bedingtes Nullintervall aus geraden Seeds mit Endwert 12

**Beedbyte · Quellenpaket v1**

Jordi Gartner veröffentlicht diese Arbeit über Beedbyte. Deutsch ist ein Übersetzungsentwurf ohne dokumentierte menschliche Sprachprüfung.

## Ergebnis

Es gelte, dass ein gerader Seed mit Endwert 12 `(K0,z0,c)` die endlichen Bedingungen der formalen Aussage erfüllt: `K0≥26` ist gerade; `z0≥3` ist ungerade und `z0+2<K0`; die Tags an geraden Indizes bilden eine Permutation von `0,…,K0`, jene an ungeraden Indizes eine Permutation von `0,…,K0−1`, und die benachbarten Summen eine Permutation von `0,…,2K0−1`; der Mitteltag ist `K0`, das lokale Tagmuster ist `[1,0,0,2]`, und der letzte Tag ist 12. Für jedes `t≥0` sei `K=K0+24t`. Zu jeder ganzzahligen Tiefe

`K0−z0−1+20t ≤ d ≤ K0−z0+22t`

gibt es eine konventionell graziöse Beschriftung mit dem Wert 0 am ausgewählten Knoten auf jedem der beiden benannten neuen K-Arme. Für jedes Ziel wird eine eigene Beschriftung verwendet. Dies gilt, wenn der Pfadmittelpunkt mit einem vorgegebenen Wurzelknoten `r` eines beliebigen endlichen Graphen `H` identifiziert wird, für den eine konventionell graziöse Beschriftung `g` mit `g(r)=0` vorliegt. `H` muss weder ein Baum noch zusammenhängend sein; seine Beschriftung muss nicht alle Werte annehmen. Über alte Knoten von `H` wird nichts ausgesagt, und gleichzeitige Nullwerte werden nicht behauptet.

## Konkrete Seeds und D8-Naht

Die enthaltenen Seed-Daten führen die konkreten Fälle `(K0,z0)=(26,5),(28,9),(30,3)` auf. Die zugehörigen Intervalle sind `[20+20t,21+22t]`, `[18+20t,19+22t]` und `[26+20t,27+22t]`. Der formale Quelltext beweist die Seed-Prüfungen und Intervallspezialisierungen für K28 und K30. K26 ist der zuvor eingefrorene konkrete Seed-Datensatz und wird in diesem Quellumfang nicht als neuer Satz ausgegeben. Nur für K30 beginnt die exakte D8-Naht bei `t=4`; dann verbinden sich beide Garantien zu `2≤d≤27+22t` auf jedem neuen Arm für alle `t≥4`. Für K26 und K28 wird in diesem Paket keine Naht behauptet.

Das Ergebnis setzt einen geeigneten Seed voraus. Es beweist weder dessen Existenz für jedes gerade `K0` noch eine Aussage zu jeder Tiefe, jeder geraden Armlänge, alten Knoten oder zwei gleichzeitigen Nullwerten. Ein historischer Prioritätsanspruch wird nicht erhoben.

## Beweis, frühere Konstruktionen und Prüfung

Die Seed-Familie verwendet die etablierten B2/B4-Einfügungsgadgets für q24 und die bereits bekannte Mittelpunkts-Alpha-Pfadverklebung mit einer gewurzelten graziösen Beschriftung. Die allgemeine Alpha-Verklebung geht auf Huang–Kotzig–Rosa zurück; ausdrücklich formuliert wird sie in [Panpa, Imnang und Wasuanankul (2025), Satz 2.5](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777) und [Shan–Zhong (2026), Lemma 1](https://arxiv.org/html/2605.14295v2). Siehe außerdem [Barrientos (2022), *On the generation of alpha graphs*](https://www.jacodesmath.com/index.php/jacodesmath/article/view/194) sowie [Barrientos–Minion (2019), §2.2](https://digitalcommons.georgiasouthern.edu/tag/vol6/iss1/4/). Das Paket beansprucht weder eine neue allgemeine Verklebungskonstruktion noch historische Priorität.

Die bedingte Familie, die K28/K30-Seeds und die K30-Naht sind in Lean 4.34.0 bewiesen. Eine getrennte interne Prüfung aus kopierten Quellen kompilierte alle 84 Module, prüfte neun zentrale Axiomenabschlüsse gegen die üblichen Lean-Axiome und verwarf zehn falsche semantische Kontrollen. Dies sind projektinterne Prüfungen, keine externe Begutachtung oder Peer-Review. Zur Vertrauensbasis gehören Leans Kernel, Compiler und Standardbibliothek. `python verify_package.py` prüft die Paketintegrität. Ein neuer Lean-Build lässt sich mit `python -B build.py --lean /path/to/lean --output /new/outside/package/objects` starten; erforderlich ist das gepinnte Lean 4.34.0 (SHA256 `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`), und die kompilierten Quellen werden in ein neues Ausgabeverzeichnis geschrieben. Die genauen Berichte und Seed-Daten stehen unter `evidence/`; Prüfsummen sind in `PAYLOAD-SHA256.json` aufgeführt.

KI-Werkzeuge unterstützten die dokumentierte Entwicklung des Lean-Beweises und der Prüfscripte sowie die Erstellung dieser deutschen und chinesischen Übersetzungsentwürfe.

Version 1 ergänzt das bedingte Seed-Nullintervall mit Endwert 12, die Spezialisierungen für K28 und K30 sowie das K30-Ergebnis zur D8-Naht.
