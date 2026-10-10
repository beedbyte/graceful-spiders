# Jeder Knoten der Spinne mit fester Armlänge 23

Beedbyte. Jordi Gartner veröffentlicht diese Arbeit über Beedbyte.

**Übersetzungsentwurf — noch nicht sprachlich geprüft.** Für jedes `n ≥ 2` und `m ≥ 0` kann jeder tatsächlich benannte Knoten von `S(23^n,1^m)` jeweils den Wert 0 in einer graziösen Beschriftung erhalten. Dazu gehören das Zentrum, jede Tiefe auf jedem benannten Arm mit 23 Kanten und jedes vorhandene Einheitsblatt. Für verschiedene Zielknoten dürfen verschiedene Beschriftungen verwendet werden. Die Aussage betrifft nur die feste Armlänge 23; sie behauptet dies nicht für alle ungeraden Armlängen.

Der Beweis verbindet vollständige Mittelpunkt-Alpha-Wege auf 47 Knoten mit einem Residuum, dessen Zentrum mit 0 beschriftet ist, und der bekannten Alpha-Verklebung. Explizite Zertifikate decken die Tiefen ab, die ältere projektinterne Konstruktionen bei dieser festen Länge nicht lieferten. Der Pfadfall `n=2,m=0` folgt aus Rosas Pfadergebnis, und der Fall mit einem zentralen Einheitsblatt `n=2,m=1` aus Luiz–Campos–Richter; die Huang–Kotzig–Rosa-Verklebung ist klassisch. Cattells ursprüngliche vollständige Wegkonstruktion wurde für die gleichzeitig benötigten Mittelpunkt- und Extremwertbedingungen nicht abschließend geprüft. Die weltweite Priorität der vollständigen Aussage bleibt daher ungeklärt.

Ältere Quellen: [Luiz–Campos–Richter, Lemma 4 und Satz 14](https://ic.unicamp.br/~reltech/2017/17-12.pdf); [Cattell, *Graceful labellings of paths*](https://www.sciencedirect.com/science/article/pii/S0012365X07001215). Die erste Quelle gibt auch die früheren Pfad- und Verklebungsbausteine wieder.

KI-Werkzeuge unterstützten Konstruktion und Beweisentwicklung, Programmierung, Lean-Formalisierung, Zertifikatsprüfung und Quellenvergleich. Die 27 kopierten Lean-Module wurden in einer getrennten projektinternen Prüfung erfolgreich neu kompiliert; fünf semantische Gegenproben schlugen wie erwartet fehl. Diese Prüfungen sind keine externe wissenschaftliche Begutachtung.
