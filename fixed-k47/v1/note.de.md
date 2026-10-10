# Null-Rotierbarkeit von Spinnen mit Armen der Länge 47

> **Entwurf: deutsche Übersetzung; sprachlich nicht geprüft.**

Jordi Gartner veröffentlicht diese Arbeit über Beedbyte.

Sei `S(47^n,1^m)` der Baum mit einem Zentrum, `n` einzeln benannten Armen aus jeweils 47 Kanten und `m` einzeln benannten ursprünglichen Blättern am Zentrum. Für jedes `n ≥ 2` und `m ≥ 0` kann jeder tatsächlich vorhandene Knoten – das Zentrum, jede Tiefe von 1 bis 47 auf jedem benannten Arm und jedes der `m` vorhandenen Blätter – in einer graziösen Beschriftung den Wert 0 erhalten. Die Beschriftung darf vom ausgewählten Knoten abhängen. Der Graph hat `N=47n+m` Kanten; eine graziöse Beschriftung bildet seine Knoten bijektiv auf `0,…,N` und seine Kantendifferenzen bijektiv auf `1,…,N` ab.

Die Konstruktion verwendet endliche Alpha-Pfad-Zertifikate mit 95 Knoten für die Armtiefen 1–38, eine gemischte q24-Konstruktion für die Tiefen 39–42, eine q30-Konstruktion für die Tiefen 43–44, ein direktes Pfadzertifikat für Tiefe 45 und eine Endpunktkonstruktion für die Tiefen 46–47. Gesonderte Nullwurzel-Konstruktionen behandeln das Zentrum und jedes ursprüngliche Zentrumsblatt. Die Quelle behandelt die feste Armlänge 47; sie beweist kein Ergebnis für alle ungeraden Armlängen oder eine unbegrenzte q24/q30-Folge.

Die vollständigen Pfadfälle `n=2,m=0` und `n=2,m=1` wurden bereits von Luiz, Campos und Richter in [*Some families of 0-rotatable graceful caterpillars* (2017), Bericht IC-17-12](https://ic.unicamp.br/~reltech/2017/17-12.pdf) behandelt; im zweiten Fall hat der Pfad ein Blatt am Zentrum. Nullwurzel-Spinnen, Alpha-Amalgamation, Graphkomplementierung und frühere Ergebnisse zur gewöhnlichen Graziösität gleicharmiger Spinnen sind ebenfalls bekannte Hilfsmittel. [Pattersons Dissertation von 2017](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content) behandelt verwandte Anfügungen und formuliert eine allgemeine Vermutung zur Null-Rotierbarkeit von Spinnen. Ein begrenzter Vergleich klärt nicht, ob frühere Pfadkonstruktionen die hier verwendeten gemeinsamen Quellbedingungen liefern; die historische Priorität bleibt daher **UNGEKLÄRT**. Siehe auch Cattell, [*Graceful labellings of paths* (2007)](https://doi.org/10.1016/j.disc.2007.03.046), sowie Bahls, Lake und Wertheim, [*Gracefulness of families of spiders* (2010)](https://msp.org/involve/2010/3-3/involve-v3-n3-p01-s.pdf).

Die Lean-Deklarationen `GracefulBoundary.K47Full.all_vertices` und `GracefulBoundary.K47Full.all_vertices_unique_zero` formalisieren die universelle Aussage für alle tatsächlich vorhandenen Knoten und ihre Verfeinerung mit eindeutiger Nullstelle. Das reproduzierbare Paket enthält 42 bytegenau fixierte Lean-Module. Ein separates Replay mit kopiertem Quelltext kompilierte alle 42 Module mit als Fehler behandelten Warnungen, prüfte 2.201 Theorem-Abhängigkeiten einschließlich 111 privater Deklarationen anhand der Standardaxiome von Lean, testete 191 tatsächlich vorhandene benannte Knoten für `n=2,m=0/1` und verwarf sechs semantische Negativkontrollen. Dies sind projektinterne Prüfungen, keine externe Begutachtung oder wissenschaftliche Peer-Review.

## Methoden

KI-Werkzeuge unterstützten maßgeblich die Entwicklung der Quellkonstruktionen, des Prüfprogramms, die mathematische Synthese, Teile des Literaturvergleichs sowie die Erstellung deutscher und chinesischer Übersetzungsentwürfe. Der Lean-Build und die getrennten Prüfungen sind projektinterne Verifikation; sie sind keine externe wissenschaftliche Begutachtung. Jordi Gartner trägt über Beedbyte die Veröffentlichungsverantwortung.

Dieses Quellpaket enthält kein PDF.
