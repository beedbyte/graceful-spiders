# Beedbyte — zwei 95-Kanten-Arme an einem graceful Wurzelgraphen

Diese englische Reader-Note ist das Original; die deutsche und die vereinfachte chinesische Fassung sind Übersetzungsentwürfe. Jordi Gartner besitzt diese Arbeit und veröffentlicht sie über Beedbyte.

## Exakter Satz

H sei ein beliebiger endlicher indizierter Graph mit Q Kanten, einem festgelegten Knoten r und einer vorgegebenen konventionellen Graceful-Beschriftung g. Das heißt: Die Knotenlabels sind injektiv in 0..Q, die absoluten Kantendifferenzen bijektiv auf 1..Q. Es gelte g(r)=0.

Identifiziere r mit dem Mittelpunkt eines neuen Pfades mit 190 Kanten. Damit entstehen zwei getrennt benannte Arme mit je 95 Kanten; alle alten H-Knoten und -Kanten bleiben erhalten. Für jeden neuen Arm und jede physische Tiefe d=1..94 besitzt der entstandene Graph eine zielabhängige konventionelle Graceful-Beschriftung mit Null am tatsächlich ausgewählten neuen Knoten. Jede Arm-/Tiefen-Anfrage darf eine andere Beschriftung verwenden. Die Ausgangslabels sind injektiv in 0..Q+190; die Kantengewichte sind genau 1..Q+190.

H muss weder ein Baum noch zusammenhängend, alpha-beschriftet oder onto-beschriftet sein. Das nicht-onto Dreieck mit Labels 0,1,3 ist enthalten. Der Satz verlangt die vorgegebene Nullbeschriftung an der gewählten Wurzel; er beweist nicht, dass jede beliebig vorgegebene Wurzel eine solche Beschriftung zulässt. Es gibt keine Aussage zu den neuen Spitzen bei Tiefe 95, alten H-Zielknoten oder dem stärkeren onto-Knotenprädikat.

Die exakte Lean-Deklaration heißt `GracefulBoundary.K95Rooted.interior` in [source/K95Rooted.lean](source/K95Rooted.lean). Ihre Konjunktion liefert getrennte Zeugen für die tatsächlichen Graft-Knoten an den Pfadindizes 95-d und 95+d.

## Evidenz und Methoden

Das Paket enthält den mathematischen Autorbeweis, eine getrennt implementierte interne Matheprüfung, den Lean-Autorbericht und einen getrennten internen Copied-Source-Replay. Die Matheprüfung legte begrenzte Einsicht in Autorprosa offen und wird nicht als vollständig blind beschrieben. Sie verwendete keinen Autorchecker.

Der Quellreplay baute alle 59 transitiven Projektmodule aus einem leeren Objektverzeichnis mit Lean 4.34.0 und Warnungen als Fehler neu. Geprüft wurden 2.239 nach Ursprungsmodul erfasste Theorem-Axiom-Closures, ausschließlich mit den Standardaxiomen `propext`, `Classical.choice`, `Quot.sound`; der exakte Theorem-Typ; das nicht-onto Dreieck an allen 94 Tiefen beider Arme; 196 konkrete Zielaussagen; und vier wirksame Wurzel-/Spitzen-/Altknoten-/onto-Kontrollen. Keine Autor- oder Vorgängerobjekte wurden importiert. Compiler und Standardbibliothek bilden die angegebene Vertrauensgrenze; die Standardbibliothek wurde nicht neu gebaut. Dies sind projektinterne Prüfungen, keine externe wissenschaftliche Begutachtung.

KI-Werkzeuge unterstützten die dokumentierte Konstruktion und den Beweiscode, Literal- und Graphprüfungen, den getrennt beauftragten internen Quellreplay sowie diese Reader-Note-Übersetzungen. Die Publikationsverantwortung bleibt bei Jordi Gartner über Beedbyte. Exakte Artefakthashes und Prüfgrenzen stehen in [evidence-pins.json](evidence-pins.json) und den erhaltenen Evidenzberichten.

Die d-graceful Verschiebung der hohen Labels, Translation, Komplementierung und Knoten-Amalgamation sind etablierte Operationen. Die allgemeine Alpha-Knoten-Amalgamation eines alpha-beschrifteten Graphen mit einem am identifizierten Knoten mit 0 beschrifteten graceful Graphen wird von Panpa, Imnang und Wasuanankul (2025, Theorem 2.5, nach Huang–Kotzig–Rosa) sowie von Shan und Zhong (2026, Lemma 1) angegeben. Die vorliegende Konstruktion verwendet diese Operation mit dem graceful Wurzelgraphen H und einem alpha-beschrifteten Pfad. Barrientos (2020), *Alpha graphs with different pendent paths*, gedruckte S. 302–303, beschreibt die Teiltransformationen und eine engere Amalgamation mit zwei alpha-Graphen als Eingaben; siehe das [Verlags-PDF](https://www.ejgta.org/index.php/ejgta/article/download/1036/pdf_143). Das ist eine Operationsüberschneidung, kein wörtlicher Satz für beliebiges H. Keine neue primitive Operation wird behauptet. Die Priorität der exakten positionsbezogenen Graphfamilien-Aussage ist **UNKNOWN**; ein erschöpfender weltweiter Vergleich oder externe Begutachtung wird nicht behauptet. Siehe [Panpa–Imnang–Wasuanankul, Theorem 2.5](https://onlinelibrary.wiley.com/doi/10.1155/jama/5826777) und [Shan–Zhong, Lemma 1](https://arxiv.org/html/2605.14295v2).

## Reproduktion

Enthalten sind die vollständige Projekt-Importclosure mit 59 Quellen, getrennte Prüfungen, Modulreihenfolge sowie Quell- und Evidenzinventare. Die Beweisquellen sind bytegleich zu den eingefrorenen Replay-Eingängen. Starte Python 3 mit dem exakt verifizierten Windows-Lean-Programm und einem neuen oder leeren Build-Verzeichnis:

```text
python -B build.py --lean "path/to/lean.exe" --build-dir "new-empty-build-folder"
```

Die Programmdatei muss SHA256 `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2` entsprechen (Lean 4.34.0, Commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`). Dieses Skript installiert keine Software und zertifiziert keinen anderen Compiler oder eine andere Plattform. Es prüft das Paketinventar, baut frische Objekte, wiederholt Typ-/Dreiecks-/Axiomprüfungen und erwartet die Ablehnung der vier semantischen Mutanten. Es löscht nichts. `SHA256SUMS.txt` inventarisiert alle Paketdateien außer seinem eigenen exakten Wurzelpfad.

Englisch: [README.md](README.md). Vereinfachtes Chinesisch: [README.zh-CN.md](README.zh-CN.md). Alle drei Texte bewahren denselben mathematischen Umfang und dieselben Prüfgrenzen.
