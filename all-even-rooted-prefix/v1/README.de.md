# Vorgegebene Nullstellen an geraden Armen eines gewurzelten graceful Graphen

**Beedbyte · Quellpaket v1**

Jordi Gartner veröffentlicht diese Arbeit über Beedbyte.
[English](README.md) · [简体中文](README.zh.md). Die deutsche und chinesische Fassung sind Übersetzungsentwürfe ohne dokumentierte menschliche Sprachprüfung.

## Der Satz

Sei **K ≥ 20 gerade**. H sei ein endlicher Graph mit Q Kanten und einer gegebenen konventionellen graceful Beschriftung g: Die Knoten tragen verschiedene ganze Zahlen aus 0,…,Q, und die Kantendifferenzen sind genau 1,…,Q. Für eine festgelegte Wurzel r wird g(r)=0 vorausgesetzt. An r werden zwei verschiedene neue Arme mit je K Kanten angefügt; H bleibt erhalten.

Für **jeden der beiden benannten neuen Arme** und jede Tiefe **2 ≤ d ≤ D8(K)** gibt es eine eigene konventionelle graceful Beschriftung des entstandenen Graphen mit Null an diesem Knoten. Tiefe zählt Kanten ab r. Die Beschriftung darf vom Ziel abhängen; gleichzeitige Nullwerte werden nicht behauptet.

| Gerades K | D8(K) |
|---|---|
| 20–34 | 11 |
| 36–52 | 27 |
| 54–124 | 25 + 16⌊(K−35)/18⌋ |
| K ≥ 126 | 107 + 20a + 2s, wobei (K−4)/2 = 61 + 11a + s und 0 ≤ s ≤ 10 |

H muss weder ein Baum noch zusammenhängend, bipartit oder alpha-beschriftet sein. Seine Knotenwerte müssen 0,…,Q nicht vollständig ausfüllen. Eine Beschriftung mit Null an der Wurzel ist Voraussetzung, keine Folgerung aus bloßer Gracefulness. Der Satz erfasst keine alten Knoten von H, Tiefe 1, Armspitzen oder Tiefen oberhalb D8(K); er behauptet keine vollständige Null-Rotierbarkeit jedes angefügten Graphen.

## Beweis und Vorarbeiten

Die Konstruktion liefert eine Alpha-Beschriftung des Pfads mit 2K Kanten, Schranke K, Mittelpunktwert K und einem Extremwert an der gewählten Position. Anschließend erhält H die Werte K+g; Pfadwerte unter K bleiben bestehen, Werte über K werden um Q erhöht. Alte Kantendifferenzen sind 1,…,Q, neue Q+1,…,Q+2K. Pfadumkehr wählt den anderen Arm, Komplementierung des ganzen Graphen macht aus einem Maximum am Ziel die Null.

Die allgemeine Amalgamation von Alpha-Schranke und Nullwurzel ist bekanntes Verfahren, Huang–Kotzig–Rosa zugeschrieben und explizit in [Panpa, Imnang und Wasuanankul (2025), Satz 2.5](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777) sowie [Shan–Zhong (2026), Lemma 1](https://arxiv.org/html/2605.14295v2) angegeben. Siehe auch [Barrientos (2022), *On the generation of alpha graphs*, S.103](https://www.jacodesmath.com/index.php/jacodesmath/article/view/194), 9(2), 101–114, DOI 10.13069/jacodesmath.1111733. Gepaarte Null-/Schrankenanker erscheinen bereits bei [Barrientos–Minion (2019), §2.2](https://digitalcommons.georgiasouthern.edu/tag/vol6/iss1/4/).

Die weltweite Priorität der genauen uniformen Mittelpunkt-/D8-Zertifikatsfamilie und ihrer Folgerung ist **UNKNOWN (ungeklärt)**. Die eingesehenen Quellen entscheiden eine mögliche ältere Herleitung nicht. Der vollständige Originaltext von [Cattells (2007) Alpha-Pfad-Charakterisierung](https://doi.org/10.1016/j.disc.2007.03.046) war für diesen Vergleich nicht zugänglich; getrennte Freiheiten für einzelne Positionen beweisen die gemeinsame Mittelpunkt-/Extremwertbedingung nicht. Hier wird weder eine neue allgemeine Anfügeoperation noch ein negativer Graphsatz beansprucht.

## Reproduktion und Vertrauensgrenze

Der Hauptsatz heißt `GracefulBoundary.EvenRootedPrefix.all_even_prefix` in [EvenRootedPrefix.lean](source/EvenRootedPrefix.lean). Das Paket enthält alle 79 transitiven Projektquellen und neun separat geschriebene Abfrage-/Kontrollquellen. Benötigt werden Python 3.9+ und Lean **4.34.0** mit seinen Standardbibliotheken; ein weiterer Projekt-Checkout ist nicht nötig.

```text
python build.py --check
python -O build.py --check
python build.py --lean /pfad/zu/lean --output /neues/verzeichnis/ausserhalb/des/pakets
```

Das Ausgabeverzeichnis darf noch nicht existieren. Der Treiber prüft sämtliche indizierten Dateien, kompiliert alle Module mit Warnungen als Fehler in frische Objekte, prüft 3.583 Axiom-Abhängigkeiten, expandiert den tatsächlichen Graphsatz und führt 16 benannte Dreiecksfälle sowie sieben erwartete Fehlkontrollen aus. K=20,36,124,126 und ein Restdreieck mit Werten 0,1,3 prüfen Grenzen und die nicht-surjektive Konvention. Fehlkontrollen für Tiefe, Wurzel, Spitze und Surjektivität prüfen Satzannahmen, keine Graphunmöglichkeit. Kompilierte Objekte werden nicht ausgeliefert.

Die universelle Aussage ist in Lean bewiesen; die endlichen Beispiele allein begründen sie nicht. Zur Vertrauensbasis gehören die Übereinstimmung von Definitionen und Graphbeschreibung, Lean-Kernel/Werkzeugkette und die zugelassenen Axiome `propext`, `Classical.choice`, `Quot.sound`. Ein separater projektinterner Replay aus kopierten Quellen bestand. Dies sind interne Projektprüfungen, keine externe Begutachtung oder Peer Review. Die [Provenienz](provenance.json) enthält genaue Quellen- und Beleg-Hashes; vollständige historische Berichte bleiben im Projektarchiv.

## Methoden und Beiträge

KI-Werkzeuge unterstützten die dokumentierte Beweisentwicklung, Lean-Implementierung, den separaten internen Replay, den Literaturvergleich und diese Übersetzungsentwürfe. Jordi Gartner trägt über Beedbyte die Veröffentlichungsverantwortung.

Version 1 enthält den D8-Satz für alle geraden K, vollständige Lean-Abhängigkeiten und reproduzierbare Scope-Prüfungen.
