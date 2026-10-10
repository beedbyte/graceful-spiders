# Beedbyte — q48-Zwei-Flip-Familie

Version q48-two-flip-v1. Sprachlicher Entwurf der Reader Note; eine menschliche Sprachprüfung ist nicht dokumentiert. Jordi Gartner veröffentlicht diese Arbeit über Beedbyte.

Für jede ganze Zahl **t>=2** sei **k=23+24t**. Für alle **n>=2,m>=0** besitzt jeder ausgewählte benannte lange Arm von **S(k^n,1^m)** jeweils ein eigenes Graceful-Labeling mit Null an jeder der physischen Tiefen **21+22t** und **22+22t**. Die Labels sind0..nk+m, die absoluten Kantendifferenzen1..nk+m. Alle ursprünglichen kurzen Blätter bleiben im Graphen; verschiedene gewünschte Nullpositionen verwenden verschiedene Labelings.

Die Konstruktion besteht aus t-2 stationären q24-Schritten und einem abschließenden q48-Makro. Dessen Ausgabe hat veränderte Nachbarn und kann nicht über den unveränderten alten Vertrag weiter iteriert werden. Dies ist kein vollständiger Nullrotierbarkeitssatz für alle Knoten dieser Längenfolge.

Alle36 Lean-Quellen wurden aus frischen Quellkopien mit Warnungen als Fehler neu gebaut. Die1992 Satzabschlüsse verwenden nur Standardaxiome;11 Lean-Mutanten und22 mathematische Mutanten wurden zurückgewiesen. Die unbeschränkten Quantoren folgen aus symbolischen Beweisen und Lean, nicht aus endlichen Tests. Der genaue Hauptsatz heißt `GracefulBoundary.Q48Flip.selected_actual`.

Ältere Verkettungs- und Einfügungsoperationen für Graceful-Pfadpermutationen werden in [REFERENCES.md](REFERENCES.md) zugeordnet. Der Graphtransfer wird in INVENTORY.md und Lean bewiesen; die Pfadzitate liefern keine historische Zuordnung dieses Graphtransfers. Die weltweite Priorität ist **UNKNOWN**. KI-Werkzeuge unterstützten Konstruktion, Beweis und Code, getrennte interne Prüfungen sowie Übersetzung. Diese Prüfungen sind projektintern, keine externe Begutachtung oder Peer Review. Es wird keine Lizenz erteilt. Evidenz und Reproduktion stehen in [README.md](README.md).
