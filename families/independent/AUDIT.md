# Unabhaengige mathematische Pruefung der Spider-Familie

9. Oktober 2026. Oeffentliche Bearbeitung des getrennten Agentenberichts: Die mathematischen Pruefabschnitte und Ergebnisse sind erhalten. Historische Arbeitsverzeichnis- und Freigabezeilen wurden ausgelassen, der Reproduktionsbefehl wurde auf die Paketstruktur angepasst, und die historische Integritaetsnotiz wurde durch den unten angegebenen Paketnachweis ersetzt. Diese Bearbeitung ist keine wortgleiche Rohberichtskopie. Herkunft und Hash des Rohberichts stehen in `../SOURCE-README.md` und `../SOURCE-MANIFEST.json`.

## Entscheidung

**Ergebnis der getrennten Agentenpruefung:** Fuer jedes `k in {3,5,7,9}`, jedes ganze `n>=2`, jedes ganze `m>=0` und jeden vorgegebenen Knoten von `S(k^n,1^m)` existiert die behauptete grazile Beschriftung mit genau dort liegender Null. Ich habe keine Gegenbeispiele, fehlenden Nullpositionen oder Luecken im unbeschraenkten Argument gefunden. Auch das allgemeine Teilresultat fuer ungerade `k>=3` und die eng gefasste geradzahlige Pfadobstruktion bestehen die Pruefung.

**Keine Freigabe einer Neuheits-, Erstbeweis- oder Universalbehauptung:** Die Methode verwendet etablierte Bausteine. Mehrere ganze Randfamilien waren bereits 2017 bewiesen. Vollstaendige historische Prioritaet ist ungeklaert. Die Pruefung ist eine getrennte Agentenpruefung mit eigener Implementierung, keine Begutachtung durch einen externen Mathematiker und keine formale Verifikation.

## Quantoren und Konstruktion

1. **Graph und Quantoren.** Der Graph hat genau `q=nk+m` Kanten und `q+1` Knoten. Die Aussage bedeutet `fuer jeden Knoten existiert eine Beschriftung`; sie fordert keine einzige Beschriftung mit mehreren Nullen. Ein fester Satz von Pfadzeugen fuer jedes der vier k reicht aus, weil n und m nur ueber einen frei waehlbaren Restgraphen in die Komposition eingehen. Es gibt keine verdeckte Beschraenkung der Armzahl.

2. **Zentrumformel.** Fuer `h>=0` lange Arme zerlegen die geraden Tiefen eines Arms und ungeraden Tiefen des entgegengesetzt indizierten Arms jedes Labelintervall `[ak+1,(a+1)k]` disjunkt. Dies stimmt sowohl fuer gerade als auch ungerade k. Die Zentrumkanten geben genau die Vielfachen von k. Die inneren Kantendifferenzen eines Arms sind `|(h-2i)k-s|`, `1<=s<k`. Der angegebene Index b durchlaeuft genau `0,...,h-1`: positive Werte von h-2i geben die eine Paritaet absteigend, nichtpositive Werte die andere aufsteigend. So werden alle Luecken zwischen den Vielfachen jeweils genau einmal gefuellt. Bei `k=1` sind diese Luecken leer. Bei `h=0` gibt es nur den Stern, bei `h=m=0` nur das Zentrum. Die Ergaenzung von m Zentrumsblaettern durch neue Maxima ist gueltig.

3. **Alpha-Amalgamation.** Wegen der bijektiven Pfadbeschriftung sind die niedrigen Pfadlabels genau `[0,A]`, die hohen genau `[A+1,2k]`. Die vorausgesetzte Gleichheit `a(k)=A` ist entscheidend und wird von jedem verwendeten Zeugen erfuellt. Der Restbaum mit `Q=(n-2)k+m` Kanten wird auf `[A,A+Q]` verschoben. Der einzige gemeinsame Wert ist A am identifizierten Zentrum; insbesondere entsteht dort kein zusaetzlicher Knoten. Die hohen Pfadlabels werden auf `[A+Q+1,2k+Q]` verschoben. Alle Pfadkanten kreuzen die Schwelle, weshalb jede ihrer Differenzen exakt um Q waechst. Die beiden Kantendifferenzintervalle sind `[1,Q]` und `[Q+1,Q+2k]`. Damit sind Bijektivitaet und Grazilitaet fuer alle Parameter bewiesen.

4. **Extrema und beliebiger Zielarm.** Null bleibt bei der Komposition am Pfadknoten mit Label Null. Das Pfadmaximum wird zum Gesamtmaximum q. Komplementieren macht genau diesen Knoten zur Null. Vollstaendiges Vertauschen gleich langer Arme ist ein Graphautomorphismus und transportiert den Zeugen an jeden vorgegebenen Arm gleicher Tiefe. Nur die einzelnen Nullknoten zwischen verschiedenen Armen zu tauschen waere falsch; der gelieferte Code tauscht korrekt die ganzen Arme. Kurze Blaetter sind untereinander frei vertauschbar.

5. **Randfall `n=2,m=0`.** Hier gilt Q=0; G ist ein einzelner Knoten. Die Komposition ist genau der Pfadzeuge. Die Randfallbezeichnung als Pfad mit ausgezeichnetem Mittelpunkt ist im Satz ausdruecklich enthalten. Auch `n=2,m>0` ist gueltig: G ist dann ein Stern mit m Kanten. Die Konstruktion der langen Nullspitze verwendet n-1>=1 Arme und laeuft deshalb auch bei n=2 ohne Sonderannahme.

6. **Ungerade Pfadformel.** Fuer `k=2r+1`, `r>=1`, sind die vier angegebenen Labelintervalle disjunkt und vollstaendig. Die rechten Differenzen sind `1,...,2r+1`, die linken `2r+2` sowie `4r+2,4r+1,...,2r+3`. Die Mitte ist A=2r, das Maximum liegt in Tiefe 1, Null in Tiefe 2. Es gibt keinen Abhaengigkeitszirkel mit den endlichen Zertifikaten. Diese Formel beweist genau die beiden inneren Tiefen fuer jedes ungerade k.

7. **Blattanhaengen.** Nach jedem Anhaengen des neuen maximalen Labels an die bisherige Null und Komplementieren ist das neue Blatt die eindeutige Null und sein Vorgaenger das neue Maximum. Wiederholung k-mal erzeugt genau einen Arm der Laenge k. Eine weitere Komplementierung gibt Null in Tiefe k-1. Fuer das kurze Blatt wird vorab genau dieses Blatt entfernt, also m-1>=0. Diese Argumente benoetigen an sich keine ungerade Armlaenge.

8. **Vollstaendige Tiefenabdeckung.** Alle sechs JSON-Zeugen wurden ohne Vertrauen auf ihre Metadaten geprueft. Ihre Label- und Differenzmultimengen sind korrekt; Mitte, Schwelle, Nulltiefe und Maximaltiefe stimmen. Die Tiefenvereinigungen lauten:

| k | Allgemeine Tiefen | Zusaetzlich aus Zertifikaten | Ergebnis |
|---|---|---|---|
| 3 | 1,2,3 | keine | alle Tiefen |
| 5 | 1,2,4,5 | 3 | alle Tiefen |
| 7 | 1,2,6,7 | 3,4,5 | alle Tiefen |
| 9 | 1,2,8,9 | 3,4,5,6,7 | alle Tiefen |

Zentrum und vorhandene kurze Blaetter sind gesondert abgedeckt. Zusammen deckt dies jeden Knoten ab, unabhaengig davon, ob in einem degenerierten Fall die Automorphismen zusaetzliche Identifikationen erlauben.

## Getrennte geradzahlige Obstruktion

Fuer `k=2r` erzwingt Mittelpunktlabel 2r mit benachbartem Maximum 4r zuerst die Kette `2r,4r,0`. Danach erzwingen die Differenzen `4r-1,...,2r+2` die angegebene alternierende Fortsetzung bis zum Endknoten r-1. Bei Differenz `q-s` bestehen die moeglichen Paare aus `(x,q-s+x)`, `0<=x<=s`. Bis auf das angegebene Paar besitzen sie einen bereits gesaettigten Knoten. Das Zentrum kann bei einer Differenz ueber 2r nicht beteiligt sein. Nach insgesamt 2r Kanten ist die Armspitze erreicht; alle uebrigen Labels zusammen mit dem Zentrum liegen in `[r,3r]` und koennen die noch fehlende Differenz `2r+1` nicht erzeugen. Dies gilt auch fuer r=1, wo die Fortsetzungsfolge leer ist.

Die alpha-Folgerung benutzt korrekt die Groesse k+1 der Bipartitionsklasse des Mittelpunkts bei geradem k; deshalb ist dessen niedriger Alphaindex k. Die Obstruktion betrifft ausschliesslich die spezifizierte Pfadkomposition. Sie widerlegt weder gerade Spider-0-Rotierbarkeit noch andere Konstruktionen. Als unabhaengige endliche Kontrolle wurden alle 6 bzw. 5.040 Permutationen mit festem Mittelpunkt und benachbartem Maximum fuer k=2 bzw. k=4 geprueft; keine ist grazil.

## Eigene Rechenpruefung

`verify_independent.py` verwendet eigene fortlaufende Knotenindizes und eine separat formulierte Konstruktion. Es importiert weder den Suchcode noch `verify.py`; `construct.py` wird in einer zweiten Testspur lediglich als Zeugenproduzent benutzt. Die Eigenschaften werden durch explizite Fehlerpruefungen kontrolliert, die auch unter Python-Optimierung aktiv bleiben. Python-Bytecodeausgabe ist deaktiviert, damit keine Dateien im fremden Quellordner entstehen.

Reproduktion: `python -B independent/verify_independent.py` aus dem Verzeichnis `families/`.

| Pruefung | Anzahl / Abdeckung |
|---|---|
| Zentrumformel | 5.376; k=1,...,64, h=0,...,20, m in {0,1,7,50} |
| Allgemeine ungerade Pfadformel | 200; k=3,5,...,401 |
| Endliche Alpha-Zertifikate | alle sechs |
| Exakte Nullknoten, eigene Konstruktion | 16.368 |
| Exakte Nullknoten, gelieferte Konstruktion | 16.368 |
| Parameter dieser vollstaendigen Knotentests | k in {3,5,7,9}, n=2,...,12, m=0,...,7 |
| Grosse Parameter | 208 Kontrollen beider Implementierungen; (n,m)=(2,10000),(1000,0),(100,100) |
| Absichtlich ungueltige Eingaben | drei korrekt verworfen: doppelte Labels, falscher Nullknoten, falsche Alpha-Schwelle |

Alles bestand. Die Tests bestaetigen Transkription, Implementierung und Randfaelle. Die unendlichen Quantoren folgen aus dem obigen Argument, nicht aus den Testgrenzen. Der fruehere K7-Beweis verlangt n=3,m>=1 und seine eigene Schwelleninvariante; der jetzige Satz verwendet eine andere Reduktion und ist davon logisch unabhaengig. Weder alte Suchbudgets noch Suchknotenstaende werden als Beweis benoetigt oder hier neu bestaetigt.

## Literatur und Reichweite

Die nachfolgenden Aussagen wurden in den bezeichneten Originaltexten nachgelesen. Ueberdeckung ist von Prioritaet zu unterscheiden.

- Patterson (2017) gibt uniforme Zentrum-Null, Alpha-Amalgamation (mit Verweis auf Huang–Kotzig–Rosa), reversible Armblattkonstruktion und die aeltere Spider-0-Rotierbarkeitsvermutung: Corollary 2.4.3, Theorems 3.2.1 und 5.3.6, Conjecture 5.4.4. Theorem 3.3.8 betrifft Grazilitaet bei hoechstens drei nichttrivialen Armen. Diese Bausteine sind bekannt; die Vermutung ist keine bewiesene universelle Aussage. Geprueft wurde der vorhandene Volltextauszug an diesen Stellen. [Originalthese](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content).
- Luiz–Campos–Richter (2017), Technical Report IC-17-12: Lemma 4 restatiert Pfad-0-Rotierbarkeit; Theorem 14 deckt einen Pfad mit einem neuen Blatt am Mittelpunkt; Theorem 22 deckt alle Caterpillars von Durchmesser sechs. Damit sind **n=2,m=0**, **n=2,m=1** jeweils fuer jedes k, sowie **n=2,k=3 und jedes m** bereits vollstaendig 0-rotierbar. Die Hypothesen passen: bei n=2 bilden die langen Arme den Pfad, und kurze Zentrumlaetter veraendern fuer k=3 den Durchmesser sechs nicht. Die Satzformulierungen 14 und 22 wurden direkt im Original geprueft; kein vollstaendiger Neubeweis dieser Literaturarbeit. [Originalbericht](https://ic.unicamp.br/~reltech/2017/17-12.pdf).
- Rofa (2023), Corollary 3, deckt **k=3,m=0 fuer jede Armzahl**. Corollary 2 behandelt erste und letzte zwei Ebenen; Theorem 2 hat Wurzelsymmetrie- und Caterpillar-Resthypothesen. Das Paper laesst vollstaendige symmetrische Spider ab Laenge vier ausdruecklich offen. Es beweist somit nicht den gesamten k=5,7,9-Satz. [Original-PDF](https://arxiv.org/pdf/2312.16235).
- Panpa–Imnang–Wasuanankul (2025), Theorems 3.2, 3.3 und 3.4, geben Zentrum-Null bei drei Beinen, jedes Blatt als Null bei vier Beinen und Grazilitaet bei fuenf Beinen. Die Originalformulierung zaehlt **alle** Beine; die spaetere Paraphrase als fuenf nichttriviale Beine ist nicht zu uebernehmen. Die Saetze behaupten keine unbegrenzt vielen Arme mit allen inneren Nullpositionen. [Verlagstext](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777).
- Shan–Zhong (2026), Lemma 1, restatiert die verwendete Alpha-Amalgamation; Theorem 5 betrifft Grazilitaet bei hoechstens drei Armen laenger als zwei. Es beweist keine volle 0-Rotierbarkeit. Unabhaengig davon ist Grazilitaet der ganzen hier betrachteten Familie bereits aus der bekannten uniformen Zentrum-Null und dem Anhaengen maximaler Blaetter ableitbar. [Original v2](https://arxiv.org/html/2605.14295v2).

Die aktualisierte `literature.md` nennt die zusaetzlich gefundenen n=2-Ueberdeckungen korrekt. Eine Formulierung, wonach saemtliche inneren Nullpositionen aller k=5,7,9-Parameter neu waeren, waere unzulaessig. Die Originalarbeiten von 1977/1982, spaetere Zitationsketten und allgemeine Saetze zu gleichzeitig vorgeschriebenen Pfadlabels wurden nicht erschoepfend geprueft. Ein Pfadsatz, der nur einen beliebigen Nullknoten garantiert, garantiert jedenfalls nicht automatisch das zugleich benoetigte Mittelpunktlabel A.

## Integritaet des oeffentlichen Pakets

`verification.json` enthaelt die erneut berechneten Hashes der fuenf hier geprueften Paketdateien. Die Anpassungen sind in `../SOURCE-README.md` dokumentiert; `../SHA256SUMS.txt` deckt die oeffentlichen Dateien ab. Die getrennte Agentenpruefung ist keine externe Fachbegutachtung und keine formale Verifikation.
