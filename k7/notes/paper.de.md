# Null an jedem gewünschten Knoten: drei Siebenerarme mit Zentrumsblättern

Für jedes ganze `m ≥ 1` ist der Spider-Baum `S(7,7,7,1^m)` **0-rotierbar**: Jeder gewünschte Knoten kann in einer graziösen Beschriftung die Null erhalten. Fünf ausdrücklich angegebene Basisbeschriftungen, vier Komplemente und eine elementare Regel zum Anfügen von Blättern ergeben einen Beweis für jedes `m`. Der geschriebene Beweis und ein getrennt implementierter interner Prüfer wurden lokal geprüft. Die Publikationspriorität ist ungeklärt.

Der Baum besteht aus einem Zentrum, drei dort beginnenden Pfaden mit je sieben Kanten und `m` weiteren Blättern unmittelbar am Zentrum. Er hat `q=21+m` Kanten und `q+1=22+m` Knoten. Ein **graceful labeling**, auf Deutsch eine graziöse Beschriftung, ist eine Bijektion von den Knoten auf `{0,…,q}`, deren absolute Kantendifferenzen jede Zahl aus `{1,…,q}` genau einmal verwenden. Für jeden gewünschten Nullknoten darf eine andere Beschriftung gewählt werden. Der Satz verlangt keine einzelne Beschriftung, die mehrere Knoten zugleich mit Null versieht.

Diese Notiz gehört zum bestehenden [Graceful-Spider-Projekt](https://beedbyte.tech/de/research/graceful-spider-three-arms). Die bisher veröffentlichte Forschungsnotiz behandelt Armlängen drei und vier. Hier wird die 0-Rotierbarkeit für Armlänge sieben und mindestens ein zusätzliches Zentrumsblatt bewiesen. Der Satz enthält keine Aussage über `m=0`, beliebige Armlängen, andere Anzahlen langer Arme oder alle Spider. Er verlangt auch keine α-Beschriftung für jeden gewünschten Nullknoten.

## Ein kleines Zertifikat für eine unendliche Familie

Neun Knotentypen genügen: das Zentrum, die Tiefen 1 bis 7 eines langen Arms und ein kurzes Zentrumsblatt. Das Zentrum ist der einzige Knoten mit Grad größer als zwei. Der Abstand zum Zentrum unterscheidet die sieben Tiefen; der Grad unterscheidet ein kurzes Blatt von Tiefe 1 eines langen Arms. Vertauschungen der drei langen Arme und der kurzen Blätter bewegen Knoten innerhalb eines Typs. Dies sind genau die neun Knotenorbits unter Graphautomorphismen.

Die folgende Tabelle enthält fünf Basiszertifikate für `m=1`, also `q=22`. Die Armfolgen laufen vom Zentrum nach außen. `p₀` ist das ursprüngliche kurze Blatt. Eine Kante liegt auf **derselben Seite** der Schwelle `t`, wenn beide Labels höchstens `t` oder beide größer als `t` sind; andernfalls **quert** sie die Schwelle. Mit Zentrumlabel `c` setzen wir `d=c-t` für `c>t`, sonst `d=t+1-c`.

| Nullknoten | c | Arm 0 | Arm 1 | Arm 2 | p₀ | t | d |
| --- | ---: | --- | --- | --- | ---: | ---: | ---: |
| Kurzes Blatt | 22 | (1,21,2,20,3,19,4) | (8,5,12,11,16,10,14) | (9,17,7,18,6,15,13) | 0 | 0 | 22 |
| Tiefe 1 | 20 | (0,22,1,19,3,17,9) | (8,14,13,6,4,21,2) | (5,18,7,16,11,15,12) | 10 | 2 | 18 |
| Tiefe 3 | 20 | (2,19,0,22,1,21,5) | (6,3,18,7,9,14,13) | (10,16,4,17,8,15,11) | 12 | 1 | 19 |
| Tiefe 5 | 19 | (2,20,1,21,0,22,6) | (4,3,15,9,14,11,13) | (5,18,10,17,7,16,12) | 8 | 2 | 17 |
| Tiefe 7 | 19 | (3,20,2,21,1,22,0) | (4,7,16,8,14,12,13) | (5,18,6,17,10,15,11) | 9 | 3 | 16 |

Jede Zeile verwendet `0,…,22` genau einmal. Ihre Kantendifferenzen, einschließlich der Kante vom Zentrum zum ersten Eintrag jedes Arms, verwenden `1,…,22` genau einmal. Die folgenden Listen ermöglichen die unmittelbare Prüfung ohne Programm.

| Nullknoten | Differenzen Arm 0 | Differenzen Arm 1 | Differenzen Arm 2 | Kurze Blattkante |
| --- | --- | --- | --- | ---: |
| Kurzes Blatt | (21,20,19,18,17,16,15) | (14,3,7,1,5,6,4) | (13,8,10,11,12,9,2) | 22 |
| Tiefe 1 | (20,22,21,18,16,14,8) | (12,6,1,7,2,17,19) | (15,13,11,9,5,4,3) | 10 |
| Tiefe 3 | (18,17,19,22,21,20,16) | (14,3,15,11,2,5,1) | (10,6,12,13,9,7,4) | 8 |
| Tiefe 5 | (17,18,19,20,21,22,16) | (15,1,12,6,5,3,2) | (14,13,8,7,10,9,4) | 11 |
| Tiefe 7 | (16,17,18,19,20,21,22) | (15,3,9,8,6,2,1) | (14,13,12,11,7,5,4) | 10 |

Ersetzt man jedes Label `x` durch `22-x`, bleiben die Differenzen erhalten. Die neue Schwelle `21-t` vertauscht die Seiten und erhält `d`. Die Komplemente liefern das Zentrum und die Tiefen 2, 4 und 6. In den Zeilen für Tiefe 1, 3 und 5 steht das Maximum 22 jeweils in Tiefe 2, 4 und 6; dort entsteht beim Komplementieren Null. Alle verwendeten Schwellen liegen in `0,…,21`, sodass auch die komplementierten Schwellen für die folgende nullerhaltende Konstruktion zulässig sind.

| Nullorbit | Herkunft | c | t | d | Differenzen auf derselben Seite | Querende Differenzen |
| --- | --- | ---: | ---: | ---: | --- | --- |
| Zentrum | Komplement des kurzen Blatts | 0 | 21 | 22 | 1,…,21 | 22 |
| Tiefe 1 | Direkte Zeile | 20 | 2 | 18 | 1,…,17 | 18,…,22 |
| Tiefe 2 | Komplement der Tiefe 1 | 2 | 19 | 18 | 1,…,17 | 18,…,22 |
| Tiefe 3 | Direkte Zeile | 20 | 1 | 19 | 1,…,18 | 19,…,22 |
| Tiefe 4 | Komplement der Tiefe 3 | 2 | 20 | 19 | 1,…,18 | 19,…,22 |
| Tiefe 5 | Direkte Zeile | 19 | 2 | 17 | 1,…,16 | 17,…,22 |
| Tiefe 6 | Komplement der Tiefe 5 | 3 | 19 | 17 | 1,…,16 | 17,…,22 |
| Tiefe 7 | Direkte Zeile | 19 | 3 | 16 | 1,…,15 | 16,…,22 |
| Kurzes Blatt | Direkte Zeile | 22 | 0 | 22 | 1,…,21 | 22 |

Jeder Intervalleintrag bedeutet, dass jede genannte Differenz genau einmal vorkommt. Diese zusätzliche Bedingung über die graziöse Beschriftbarkeit hinaus ermöglicht die Fortsetzung.

## Das Blatt-Einfügelemma

Ein Baum mit `Q` Kanten habe eine graziöse Beschriftung `b` und einen ausgezeichneten Knoten mit Label `c`. Wähle ein ganzzahliges `0≤t≤Q`, und definiere `d` wie oben. Vorausgesetzt sei, dass die gleichseitigen Differenzen genau `1,…,d-1` und die querenden Differenzen genau `d,…,Q` sind, jeweils einmal.

Für jedes ganze `n≥0` füge `n` neue Blätter am ausgezeichneten Knoten an. Für jeden alten Knoten setze

`f(v)=b(v)` bei `b(v)≤t`, und `f(v)=b(v)+n` bei `b(v)>t`.

Die neuen Blätter erhalten `t+s` für `1≤s≤n`. Die alten niedrigen Labels, die neuen Labels und die alten hohen Labels belegen die disjunkten Intervalle `[0,t]`, `[t+1,t+n]` und `[t+n+1,Q+n]`. Somit kommt jedes Label von Null bis `Q+n` genau einmal vor. Die ursprüngliche Null bleibt am selben Knoten.

Alte gleichseitige Kantendifferenzen bleiben `1,…,d-1`. Alte querende Differenzen steigen um `n` und werden `d+n,…,Q+n`. Bei `c>t` erhält der ausgezeichnete Knoten `c+n`, und die neuen Blattkantendifferenzen sind

`(c+n)-(t+s)=d+n-s`.

Bei `c≤t` sind sie

`(t+s)-c=d+s-1`.

In beiden Fällen durchlaufen sie für `s=1,…,n` genau einmal das fehlende Intervall `d,…,d+n-1`. Für `n=0` ist es leer. Die drei Differenzintervalle sind disjunkt und ergeben gemeinsam `1,…,Q+n`. Damit ist das Lemma unmittelbar für jedes `n` bewiesen.

Wende es auf jede der neun Basen mit `Q=22` und `n=m-1` an. Der entstehende Baum ist `S(7,7,7,1^m)`, und die gewählte Basisnull bleibt erhalten. Arm- und Blattvertauschungen übertragen Null auf jeden Knoten seines Orbits. Dies beweist die behauptete 0-Rotierbarkeit für jedes `m≥1`.

Beispielsweise verschiebt man für die Tiefe-1-Zeile bei `m=3` sämtliche Labels über 2 um 2 nach oben und fügt Blätter mit 3 und 4 an. Das Zentrum erhält 22. Die neuen Differenzen sind 19 und 18; die alten gleichseitigen Differenzen bleiben `1,…,17`, und die alten querenden Differenzen werden `20,…,24`. Null bleibt in Tiefe 1. Das Beispiel veranschaulicht die Formel; das Lemma liefert die unbeschränkte Aussage.

## Was bereits bekannt war

Die graziöse Beschriftbarkeit der gesamten Familie ist durch **Brandon J. Pattersons Masterarbeit von 2017**, Theorem 3.3.8, abgedeckt. Der Satz liefert sogar α-Beschriftbarkeit bei höchstens drei Beinen länger als eins, wenn mindestens eines länger als zwei ist. Eine α-Beschriftung ist eine graziöse Beschriftung mit einer Schwelle, die jede Kante quert. Ihre Existenz legt keinen beliebigen Nullknoten fest. Pattersons Conjecture 5.4.4 vermutet 0-Rotierbarkeit für Spider außerhalb der Familie `S(3,1,1,…)`; die hier betrachtete Familie ist ein Spezialfall dieser älteren Vermutung. Der vollständige Text mit 104 PDF-Seiten steht im [Repositorium der Ball State University](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content).

Mehrere Nullpositionen folgen ebenfalls aus Pattersons Ergebnissen. Entfernt man einen gewählten Siebenerarm, bilden die beiden übrigen langen Arme `P₁₅`. Dessen Mittelpunkt kann nach dem als Theorem 3.1.3 zitierten Pfadsatz Null erhalten. Die kurzen Blätter lassen sich mit neuen Maximalwerten anfügen; das Zentrum bleibt Null. Die reversible Blattreduktion aus Theorem 5.3.6 rekonstruiert den entfernten Arm mit Null an seiner Spitze. Deren Nachbar muss das Maximum tragen, weil nur eine Kante zwischen Null und Maximum die Differenz `q` haben kann. Komplementierung liefert deshalb Null in Tiefe 6. Dies sind eigene Ableitungen aus den zitierten Sätzen, kein wörtlich aus der Arbeit übernommener Familiensatz. Auch Zentrum-Null und kurzes Blatt-Null folgen aus bekannten Zentrum-Null-Konstruktionen und elementaren Blattanfügungen. Pattersons endlicher Zensus reicht bis Ordnung 16; der kleinste Baum hier hat 23 Knoten.

**Panpa, Imnang und Wasuanankul (2025)** beweisen Zentrum-Null für Drei-Bein-Spider (Theorem 3.2), Null an jedem vorgegebenen Blatt für Vier-Bein-Spider (Theorem 3.3) und graziöse Beschriftbarkeit für Fünf-Bein-Spider (Theorem 3.4). Der Vier-Bein-Satz deckt die Blätter bei `m=1` unmittelbar ab; der Fünf-Bein-Satz deckt graziöse Beschriftbarkeit bei `m=2` ab. Diese Sätze liefern nicht alle sieben Armtiefen als Nullpositionen für jedes `m`. Siehe den [Originalartikel](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777).

**Shan und Zhong (2026)** beweisen graziöse Beschriftbarkeit, wenn bis auf drei Beine alle Beinlängen höchstens zwei sind (Theorem 5). Jeder Baum dieser Familie erfüllt die Voraussetzung. Der zitierte Satz behauptet graziöse Beschriftbarkeit und keine Null an jedem gewünschten Knoten. Siehe [arXiv:2605.14295v2](https://arxiv.org/abs/2605.14295v2).

Gegenüber diesen ausdrücklich geprüften Sätzen und Ableitungen deckt der Zertifikatbeweis die fünf weiteren inneren Tiefen 1 bis 5 als Teil aller neun Orbits ab. Dieser Vergleich ist kein Originalitätsnachweis. Weder für den Satz noch für die Basistabellen oder die allgemeine Idee einer Label-Lücke wird Priorität beansprucht. Die Quellenliste `SOURCES.md` im Prüfpaket dokumentiert die breitere Einordnung und die Grenzen der Literaturprüfung.

## Prüfung selbst ausführen

Das Beweisarchiv erhält die ursprüngliche Dateistruktur. Vom Wurzelverzeichnis des entpackten Archivs aus genügen Python ab Version 3.10 und diese Befehle; zusätzliche Pakete sind nicht nötig:

```sh
cd repro
python research-audits/graceful-k7-feasibility/verify-continuation.py
python research-audits/graceful-k7-independent/independent_check.py
```

Der erste Prüfer kontrolliert alle neun Basen, ihre Schwellenintervalle, exakte affine Kantenformeln, den reduzierten Spitzenzeugen und 900 konkrete Beschriftungen für `m=1,…,100`. Seine Abschlussmeldung enthält `9 of 9 zero-label orbits verified; reduced tip witness PASS.`

Der zweite Prüfer rekonstruiert den Graphen aus den Beinlängen und verwendet eine andere Knotendarstellung. Er importiert weder den ursprünglichen Prüfer noch Suchprogramme. Er kontrolliert Knoten- und Kantenmultimengen, exakte Formeln für jede nichtnegative Anzahl eingefügter Blätter, 54 ausdrückliche Erweiterungen und 74 Übertragungen der Null auf jeden einzelnen Knoten bei `m=1,2,5`. Außerdem prüft er einen absichtlich falschen Schwellenwert und kleinere diagnostische Baumfälle. Er endet mit `GO for mathematical statement; novelty not assessed.` Er schreibt `audit-results.json` neben seinen Quelltext; das entpackte Verzeichnis benötigt daher Schreibrechte.

Die JSON-Zertifikate und beide Prüfer genügen zur Kontrolle der Basen; die Suche muss nicht erneut laufen. Die Formeln und der Intervallbeweis tragen die Aussage für alle `m`; die endlichen Diagnosen helfen, Programmier- und Übertragungsfehler zu finden. Die [Reproduktionsmanifestdatei](../REPRO-MANIFEST.json) enthält die Dateihashes, der [Prüfbericht](../REPRO-REPORT.md) dokumentiert die Kontrollen. Das [Beweisarchiv](../graceful-k7-zero-rotatability-proof.zip) enthält die neun Reproduktionsdateien.

KI-Unterstützung kam bei Suche, Beweisentwicklung und Beweisprüfung, Programmprüfung, Textvorbereitung sowie den deutschen und chinesischen Übersetzungsentwürfen zum Einsatz. Der getrennte Prüfer und die mathematische Gegenprüfung sind intern; sie sind keine externe Fachbegutachtung und keine Formalisierung in einem Beweisassistenten. Die deutschen und chinesischen Texte bleiben Übersetzungsentwürfe.
