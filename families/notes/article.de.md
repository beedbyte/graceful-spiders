# Vorgegebene Null in Spinnenfamilien mit gleich langen Armen

**Forschungsnotiz · 9. Oktober 2026. Deutsche Übersetzung noch nicht menschlich sprachlich geprüft.**

Wir geben einen expliziten Beweis mit sechs endlichen Pfadzertifikaten für die 0-Rotierbarkeit von Spinnen mit Armlängen 3, 5, 7 und 9, beliebig vielen gleich langen Armen und beliebig vielen zusätzlichen Zentrumsblättern. Der Beweis verwendet bekannte Konstruktionen für Zentrum-Null, Alpha-Amalgamation und Blattanfügung. Die Aussage für unbeschränkte Parameter folgt aus den Formeln und der vollständigen Abdeckung aller Knotentiefen. Endliche Rechnungen kontrollieren die Zertifikate und die Implementierungen. Eine getrennte interne Agentenprüfung mit eigener Implementierung hat keine Lücke gefunden; sie ersetzt keine externe Fachbegutachtung.

## 1. Begriffe und Satz

Ein Baum mit `q` Kanten heißt **grazil**, wenn es eine bijektive Knotenbeschriftung mit `0,…,q` gibt, deren absolute Kantendifferenzen genau `1,…,q` sind. Er heißt **0-rotierbar**, wenn für jeden vorgegebenen Knoten `v` eine solche Beschriftung mit `f(v)=0` existiert. Die Beschriftung darf von `v` abhängen.

Mit `S(k^n,1^m)` bezeichnen wir den Baum mit einem ausgezeichneten Zentrum, `n` Armen mit jeweils `k` Kanten und `m` zusätzlichen Blättern direkt am Zentrum. Die Hochzahlen geben Anzahlen an, keine Potenzen. Die Tiefe eines Knotens auf einem langen Arm ist sein Abstand vom Zentrum. Der Baum hat `q=nk+m` Kanten und `q+1` Knoten. Der Fall `n=2,m=0` ist ein Pfad mit ausgezeichnetem Mittelpunkt; wir schließen ihn ein, auch wenn eine Definition von „Spinne“ mindestens drei Beine verlangt.

**Satz.** Für jedes `k∈{3,5,7,9}`, jede ganze Zahl `n≥2`, jede ganze Zahl `m≥0` und jeden Knoten `v` von `S(k^n,1^m)` gibt es eine bijektive Beschriftung mit `0,…,nk+m`, die `v` die Null zuweist und jede Kantendifferenz `1,…,nk+m` genau einmal erzeugt.

Insbesondere ist `S(9,9,9,1^m)` für jedes `m≥0` erfasst. Gegenüber der früheren K7-Notiz für `k=7,n=3,m≥1` umfasst die jetzige Konstruktion beliebige `n≥2` und auch `m=0`. Der neue Beweis ist von der früheren Schwelleninvariante logisch unabhängig.

Der frühere Satz für `S(4,4,4,1^m)` mit `m≥1` bleibt ein getrenntes Ergebnis. Der hier bewiesene Familiensatz erweitert `k=4` nicht auf beliebig viele lange Arme.

**Allgemeines Teilresultat.** Für jedes ungerade `k≥3`, `n≥2` und `m≥0` kann die Null am Zentrum, in den Tiefen `1,2,k−1,k` eines beliebigen langen Arms und an jedem vorhandenen kurzen Blatt vorgeschrieben werden. Zusammenfallende Tiefen werden nur einmal gezählt.

Der vollständige Satz betrifft genau die vier angegebenen Armlängen. Er behauptet keine vollständige 0-Rotierbarkeit für alle ungeraden oder geraden Armlängen und keine Aussage für ungleich lange Arme. Die schließlich erhaltene Beschriftung muss keine Alpha-Beschriftung sein.

## 2. Eine explizite Formel für Zentrum-Null

Diese Formel ist eine Spezialisierung der bekannten Beschriftung wurzelsymmetrischer Bäume; vgl. Rofa, Satz 1. Wir verifizieren sie direkt.

Für ganze Zahlen `k≥1`, `h≥0` und `m≥0` beschriften wir das Zentrum von `S(k^h,1^m)` mit Null. Die langen Arme erhalten Indizes `i=0,…,h−1`, ihre Tiefen Indizes `j=1,…,k`. Setze

```text
b(i,j) = (h−i)k − (j−1)/2    für ungerades j,
b(i,j) = ik + j/2            für gerades j.
```

Die kurzen Blätter bekommen die Labels `hk+1,…,hk+m`.

In jedem Block `[ak+1,(a+1)k]`, `a=0,…,h−1`, liefern die geraden Tiefen von Arm `a` die ersten `⌊k/2⌋` Labels. Die ungeraden Tiefen von Arm `h−1−a` liefern die letzten `⌈k/2⌉` Labels. Somit verwenden die langen Arme genau `1,…,hk`, jeweils einmal.

Die Kanten am Zentrum haben Differenzen `(h−i)k` und liefern alle positiven Vielfachen von `k` bis `hk`. Die inneren Kantendifferenzen auf Arm `i` sind

```text
|(h−2i)k−s|,    1≤s≤k−1.
```

Schreibe `a=h−2i`. Diese Differenzen bilden den Block `[bk+1,(b+1)k−1]`, wobei `b=a−1` für `a>0` und `b=−a` für `a≤0` gilt. Beim Durchlaufen aller Arme sind die Werte von `b` eine Permutation von `0,…,h−1`: Positive `a` liefern `h−1,h−3,…`; nichtpositive `a` liefern die verbleibende Parität aufsteigend. Die Blöcke und die Vielfachen von `k` zerlegen daher `1,…,hk`. Die kurzen Blätter ergänzen die Differenzen `hk+1,…,hk+m`.

Damit ist die Beschriftung grazil und hat Null am Zentrum. Für `k=1` sind die inneren Differenzblöcke leer. Für `h=0` bleibt ein Stern; für `h=m=0` bleibt allein das Zentrum. Diese Randfälle sind eingeschlossen. Insbesondere folgt die gewöhnliche Grazilität der gesamten Familie bereits aus dieser bekannten Konstruktion, auch für beliebige Armlängen `k`.

## 3. Alpha-Pfad-Komposition mit festgehaltenen Extrema

Wir verwenden die bekannte Alpha-Amalgamation und halten ausdrücklich fest, wo Null und Maximum liegen. Eine neue Kompositionsmethode wird nicht beansprucht.

Sei `H=P_(2k+1)` der Pfad mit Positionen `0,…,2k` und ausgezeichnetem Zentrum an Position `k`. Eine grazile Beschriftung `a` von `H` sei eine Alpha-Beschriftung mit Schwelle `A`: Jede Kante verbindet ein Label höchstens `A` mit einem Label größer als `A`. Zusätzlich fordern wir

```text
a(k)=A.
```

Sei `G=S(k^(n−2),1^m)` mit der Zentrum-Null-Beschriftung `b` aus Abschnitt 2, und setze `Q=(n−2)k+m`. Identifiziere die beiden Zentren und definiere

```text
f(v)=b(v)+A       auf G,
f(v)=a(v)         auf H, falls a(v)≤A,
f(v)=a(v)+Q       auf H, falls a(v)>A.
```

Am gemeinsamen Zentrum stimmen die Regeln überein. Die Labels von `G` sind `[A,A+Q]`, die niedrigen Pfadlabels `[0,A]` und die hohen Pfadlabels `[A+Q+1,2k+Q]`. Nur `A` tritt in beiden Regeln auf, und zwar am identifizierten Knoten. Deshalb ist `f` eine Bijektion auf `[0,nk+m]`.

Die Kantendifferenzen in `G` bleiben `1,…,Q`. Jede Pfadkante kreuzt die Alpha-Schwelle, sodass ihre Differenz genau um `Q` wächst. Die Pfadkanten liefern folglich `Q+1,…,Q+2k`. Dies beweist die Grazilität.

Der Pfadknoten mit `a=0` behält Null. Der Pfadknoten mit `a=2k` erhält das Gesamtmaximum `nk+m`. Durch Komplementieren, also durch Ersetzen jedes Labels `x` durch `nk+m−x`, wird dieser zweite Knoten zur Null; alle Kantendifferenzen bleiben erhalten.

**Pfadreduktion.** Jede Tiefe, in der Null oder `2k` auf einem solchen Alpha-Pfad mit Mittelpunktlabel `A` liegt, ist für alle `n≥2,m≥0` eine zulässige vorgegebene Nulltiefe in `S(k^n,1^m)`. Durch Vertauschen ganzer gleich langer Arme gelangt sie auf jeden gewünschten Arm. Für `Q=0`, also `n=2,m=0`, ist die Konstruktion genau der ursprüngliche Pfad. Für `n=2,m>0` ist der Restbaum `G` ein Stern mit `m` Kanten.

Die gewöhnliche 0-Rotierbarkeit von Pfaden allein genügt für diese Reduktion nicht: Gleichzeitig muss das Mittelpunktlabel genau die Alpha-Schwelle sein.

## 4. Eine uniforme Formel für die Tiefen eins und zwei

Sei `k=2r+1` mit `r≥1`. Beschrifte das Zentrum des Pfades `H` mit `A=2r`. Auf dem linken Arm setze

```text
a_L(2j+1)=4r+2−j,    0≤j≤r,
a_L(2j)=j−1,         1≤j≤r.
```

Auf dem rechten Arm setze

```text
a_R(2j+1)=2r+1+j,    0≤j≤r,
a_R(2j)=2r−j,       1≤j≤r.
```

Die niedrigen Labels sind das Zentrum `2r`, die linken geraden Labels `0,…,r−1` und die rechten geraden Labels `r,…,2r−1`. Die hohen Labels bilden links `[3r+2,4r+2]` und rechts `[2r+1,3r+1]`. Diese Intervalle sind disjunkt und vollständig; jede Kante kreuzt die Schwelle `A=2r`.

Die rechten Kantendifferenzen lauten vom Zentrum nach außen `1,2,…,2r+1`. Die erste linke Differenz ist `2r+2`, die übrigen sind `4r+2,4r+1,…,2r+3`. Somit kommt jede Differenz `1,…,4r+2=2k` genau einmal vor. Links liegt das Maximum `2k` in Tiefe eins und Null in Tiefe zwei. Die Pfadreduktion liefert daher beide Nulltiefen für jedes ungerade `k≥3` und alle zulässigen `n,m`.

## 5. Zentrum, Armspitzen, ihre Vorgänger und kurze Blätter

Das Zentrum ist durch Abschnitt 2 abgedeckt. Für die weiteren Positionen verwenden wir die reversible Blattkonstruktion, die Patterson in Satz 5.3.6 behandelt.

Hat ein graziler Baum `q` Kanten und Null an einem bestimmten Knoten, füge dort ein Blatt mit Label `q+1` an. Die alten Differenzen bleiben erhalten, und die neue Kante hat Differenz `q+1`. Komplementiere anschließend alle Labels über `q+1`. Das neue Blatt hat nun Null; der vorherige Nullknoten hat das neue Maximum.

Für einen ausgewählten langen Arm beginne mit Zentrum-Null auf `S(k^(n−1),1^m)`. Wende die Operation `k`-mal an, wobei das nächste Blatt jeweils am aktuellen Nullende angefügt wird. So entsteht genau der entfernte Arm mit Null an seiner Spitze. Sein Vorgänger hat Label `nk+m`; eine abschließende Komplementierung setzt daher die Null in Tiefe `k−1`.

Für ein ausgewähltes kurzes Blatt bei `m≥1` beginne mit Zentrum-Null auf `S(k^n,1^(m−1))` und wende die Operation einmal an. Das neue kurze Blatt hat Null. Kurze Blätter können untereinander vertauscht werden.

Diese Argumente gelten auch für gerade Armlängen und für Startbäume, die ein Pfad oder ein einzelner Knoten sind. Gemeinsam mit Abschnitt 4 beweisen sie das allgemeine Teilresultat für ungerade `k`. Es folgt aus Konstruktionen für alle Parameter und wird nicht aus endlichen Tests extrapoliert.

## 6. Sechs endliche Alpha-Pfad-Zertifikate

Die folgenden Pfadlabels stehen in der Reihenfolge vom linken zum rechten Endpunkt. Der Eintrag mit Index `k`, bei Zählung ab Null, ist das Zentrum und hat Label `A=k−1`. Die letzten Spalten geben die Abstände der Labels Null und `2k` vom Zentrum an. Die exakten Daten stehen auch in `certificates.json`.

| k | Pfadlabels von einem Endpunkt zum anderen | Nulltiefe | Maximaltiefe |
|---:|---|---:|---:|
| 5 | `(9,1,10,0,7,4,5,3,8,2,6)` | 2 | 3 |
| 7 | `(12,3,13,1,14,0,11,6,7,5,8,4,10,2,9)` | 2 | 3 |
| 7 | `(10,1,14,0,12,2,13,6,7,5,8,4,9,3,11)` | 4 | 5 |
| 9 | `(15,3,16,2,17,1,18,0,11,8,9,7,13,4,14,6,10,5,12)` | 2 | 3 |
| 9 | `(16,2,17,1,18,0,13,4,10,8,9,6,14,3,15,5,12,7,11)` | 4 | 5 |
| 9 | `(17,1,18,0,15,4,12,7,9,8,11,5,14,2,16,3,13,6,10)` | 6 | 7 |

Jede Zeile verwendet genau `0,…,2k` und alterniert über der Schwelle `A=k−1`. Die aufeinanderfolgenden Kantendifferenzen lauten:

| k | Nulltiefe | Kantendifferenzen in Pfadreihenfolge |
|---:|---:|---|
| 5 | 2 | `(8,9,10,7,3,1,2,5,6,4)` |
| 7 | 2 | `(9,10,12,13,14,11,5,1,2,3,4,6,8,7)` |
| 7 | 4 | `(9,13,14,12,10,11,7,1,2,3,4,5,6,8)` |
| 9 | 2 | `(12,13,14,15,16,17,18,11,3,1,2,6,9,10,8,4,5,7)` |
| 9 | 4 | `(14,15,16,17,18,13,9,6,2,1,3,8,11,12,10,7,5,4)` |
| 9 | 6 | `(16,17,18,15,11,8,5,2,1,3,6,9,12,14,13,10,7,4)` |

Diese Folgen sind Permutationen von `1,…,2k` und lassen sich unmittelbar nachprüfen. Die Pfadreduktion macht jede angegebene Null- und Maximaltiefe für alle `n≥2,m≥0` zu einer zulässigen Nulltiefe.

| k | Tiefen aus den allgemeinen Konstruktionen | Zusätzliche Tiefen aus Zertifikaten | Abdeckung |
|---:|---|---|---|
| 3 | 1,2,3 | keine | 1 bis 3 |
| 5 | 1,2,4,5 | 3 | 1 bis 5 |
| 7 | 1,2,6,7 | 3,4,5 | 1 bis 7 |
| 9 | 1,2,8,9 | 3,4,5,6,7 | 1 bis 9 |

Zentrum und vorhandene kurze Blätter sind gesondert abgedeckt. Durch Vertauschen ganzer gleich langer Arme ist jeder Knoten jeder Tiefe erreichbar. Wir benötigen keine Behauptung, dass diese Positionen in jedem degenerierten Fall genau den Automorphismenbahnen entsprechen. Jeder Knoten wurde ausdrücklich behandelt. Damit ist der Satz bewiesen.

## 7. Eine Obstruktion für diese Methode bei geraden Armlängen

**Obstruktion.** Für `k=2r≥2` gibt es keine grazile Beschriftung von `P_(2k+1)`, bei der der Mittelpunkt Label `k` und ein Nachbar des Mittelpunkts Label `2k` trägt.

Schreibe `q=4r`. Der Mittelpunkt hat das vorgeschriebene Label `2r`. Sein Nachbar mit Label `q` muss außerdem mit Null verbunden sein, damit Differenz `q` entsteht. Der Arm beginnt daher mit `(2r,q,0)`, und der Knoten mit Label `q` hat bereits beide Nachbarn. Differenz `q−1` zwingt den anderen Nachbarn von Null zu Label `q−1`, da das alternative Paar `(1,q)` nicht mehr verfügbar ist. Die größten noch fehlenden Differenzen erzwingen absteigend die Kette

```text
2r, 4r, 0, 4r−1, 1, 4r−2, 2, …, 3r+1, r−1.
```

Die Induktion schließt konkurrierende Paare aus: Vor dem Erzwingen von Differenz `q−s` liegen alle Labels außerhalb des noch unbenutzten mittleren Intervalls auf dieser Kette. Alle früheren Kettenknoten außer dem aktuellen Ende und dem Mittelpunkt haben bereits ihren vollen Pfadgrad. Für gerades `s=2j` ist das einzige verfügbare Paar mit Differenz `q−2j` das Paar `(j,q−j)`; für ungerades `s=2j+1` ist es `(j,q−j−1)`. Der Mittelpunkt kann bei keiner dieser Differenzen beteiligt sein, weil sein Abstand zu jedem Label höchstens `2r` beträgt, die erzwungenen Differenzen aber größer als `2r` sind. Jeder Schritt verlängert somit die angegebene Kette, bis sie `2r=k` Kanten hat.

Der letzte Knoten mit Label `r−1` ist jetzt der Pfadendpunkt. Alle Knoten dieses Arms außer dem Mittelpunkt sind gesättigt. Die noch fehlende Differenz `2r+1` kann auf diesem Arm nicht mehr entstehen. Die verbleibenden Knoten haben zusammen mit dem Mittelpunkt Labels in `[r,3r]`, einem Intervall der Breite `2r`. Auch dort ist Differenz `2r+1` unmöglich. Das ist ein Widerspruch. Für `r=1` ist die erzwungene Fortsetzung nach `(2r,q,0)` leer; derselbe Schluss gilt.

Bei einer Alpha-Beschriftung dieses Pfades mit Mittelpunkt auf der niedrigen Seite enthält diese Bipartitionsklasse `k+1` Knoten. Wegen der Bijektivität muss die Alpha-Schwelle daher `k` sein. Die angegebene Pfadkomposition kann folglich bei geradem `k` keine Null in Tiefe eins erzeugen, indem sie dort das Pfadmaximum platziert. Sie kann dort auch nicht die Pfadnull platzieren, weil Mittelpunkt und seine Nachbarn auf verschiedenen Alpha-Seiten liegen.

Dies ist eine Grenze der genau beschriebenen Pfadreduktion. Daraus folgt keine fehlende 0-Rotierbarkeit gerader Spinnen und kein Hindernis für andere grazile Konstruktionen. Frühere Spinnenzertifikate für `k=4` zeigen bereits diese Unterscheidung.

## 8. Reproduktion und interne Prüfungen

Die Prüfer benötigen Python 3.10 oder neuer und nur die Standardbibliothek. Der ursprüngliche Prüfer verwendet Python-Assertions und muss ohne die Optimierungsoption `-O` ausgeführt werden. Beide Prüfer schreiben Ergebnisdateien; das entpackte Paketverzeichnis muss daher beschreibbar sein.

Die vollständige Konstruktion, die sechs Zertifikate und beide Prüfer gehören zum [Reproduktionspaket](../README.md). Es benötigt Python 3.10 oder neuer und nur die Standardbibliothek. Führe nach dem Herunterladen des Repositorys aus dessen Hauptverzeichnis aus:

```text
python -B families/verify.py
python -B families/independent/verify_independent.py
python -B families/construct.py 9 3 1 5
```

Der dritte Befehl erzeugt eine Beschriftung für drei Arme mit je neun Kanten, ein kurzes Blatt und Null in Tiefe fünf. Die [sechs Zertifikate](../certificates.json) sind direkt enthalten; zur Prüfung wird kein Suchprogramm benötigt. Der [Herkunftsnachweis](../SOURCE-README.md) dokumentiert die Anpassungen gegenüber dem internen Arbeitspaket. Die [Reproduktionsprüfung](../REPRODUCIBILITY.md) beschreibt die Paketkontrollen.

Die deterministische Suche der ursprünglichen Sitzung fand die drei Zertifikate für Armlänge neun nach `209029`, `256000` und `470757` DFS-Eintritten; für Armlänge fünf und die beiden Zertifikate für Armlänge sieben waren es `72`, `4017` und `4073`. Diese historischen Suchzahlen sind für den Beweis nicht erforderlich. Bei ausgeschöpftem Suchbudget lautete das Ergebnis `UNKNOWN`; `EXHAUSTED` bezog sich nur auf die gewählten Pfad-, Mittelpunkt-, Null-, Maximum- und Bipartitionsbedingungen, nicht auf sämtliche Beschriftungen der Spinne.

`verify.py` baut jeden Graphen neu auf und prüft die Multimengen der Knotenlabels und Kantendifferenzen unabhängig von der Suche. Es verwendet `construct.py` nur zur Erzeugung von Beschriftungen und kontrolliert den exakt angeforderten Nullknoten. Das protokollierte Ergebnis umfasst:

| Prüfung im ursprünglichen Paket | Anzahl / Abdeckung |
|---|---|
| Zentrumformel | 1.440 Kontrollen |
| Allgemeine ungerade Pfadformel | 100 Kontrollen |
| Endliche Pfadzertifikate | alle sechs |
| Vollständige repräsentative Beschriftungen | 652 |
| Exakt vorgeschriebene Nullknoten | 2.352 |
| Vollständige Knotentests | alle Knoten für `k∈{3,5,7,9}`, `n∈{2,3,4,5,8}`, `m∈{0,1,2,5}`; zusätzlich größere Beispiele |
| Absichtlich beschädigte Eingaben | zwei korrekt verworfen |

Die ursprüngliche Konstruktion und ihr Prüfer entstanden in derselben Forschungssitzung. Zusätzlich wurde eine getrennte interne Agentenprüfung durchgeführt. Ihr Skript verwendet eigene fortlaufende Knotenindizes und eine separat formulierte Konstruktion; weder Suchcode noch `verify.py` werden importiert. In einer zweiten Testspur dient `construct.py` lediglich als Zeugenproduzent. Explizite Fehlerprüfungen bleiben auch unter Python-Optimierung aktiv.

Reproduktion der getrennten Prüfung vom Projektverzeichnis aus:

```text
python -B families/independent/verify_independent.py
```

| Getrennte interne Prüfung | Anzahl / Abdeckung |
|---|---|
| Zentrumformel | 5.376; `k=1,…,64`, `h=0,…,20`, `m∈{0,1,7,50}` |
| Allgemeine ungerade Pfadformel | 200; `k=3,5,…,401` |
| Endliche Alpha-Zertifikate | alle sechs |
| Exakte Nullknoten, eigene Konstruktion | 16.368 |
| Exakte Nullknoten, gelieferte Konstruktion | 16.368 |
| Parameter der vollständigen Knotentests | `k∈{3,5,7,9}`, `n=2,…,12`, `m=0,…,7` |
| Große Parameter | 208 Kontrollen beider Implementierungen; `(n,m)=(2,10000),(1000,0),(100,100)` |
| Absichtlich ungültige Eingaben | drei korrekt verworfen: doppelte Labels, falscher Nullknoten, falsche Alpha-Schwelle |

Alle Prüfungen bestanden. Für die gerade Pfadobstruktion wurden außerdem sämtliche `6` beziehungsweise `5.040` Permutationen mit festem Mittelpunkt und benachbartem Maximum bei `k=2` beziehungsweise `k=4` geprüft; keine war grazil.

Die getrennte Prüfung hat auch die unbeschränkten schriftlichen Argumente, die Quantoren, die Vollständigkeit der Nullpositionen und die Randfälle nachvollzogen. Endliche Testgrenzen begründen jedoch keine unendlichen Quantoren. Diese folgen aus dem Intervallbeweis, der Komposition und der vollständigen Tiefenabdeckung. Die Rechnungen kontrollieren Übertragung und Implementierung. Es handelt sich weder um formale Verifikation mit einem Beweisassistenten noch um externe mathematische Begutachtung.

Das [Quellenmanifest](../SOURCE-MANIFEST.json) dokumentiert die Herkunft der Dateien; die [SHA-256-Liste](../SHA256SUMS.txt) ermöglicht die Integritätsprüfung des Pakets. Der [Bericht der getrennten Agentenprüfung](../independent/AUDIT.md) beschreibt den mathematischen Prüfumfang. Nach der Literaturergänzung wurde der interne Prüfer erneut ausgeführt; Beweis, Konstruktion, ursprünglicher Prüfer und Zertifikate blieben dabei identisch.

## 9. Bekannte Ergebnisse und genaue Überdeckungen

Die gezielte Literaturprüfung trennt die Grazilität der Familie von der stärkeren Aussage über jeden vorgeschriebenen Nullknoten. Die Grazilität für alle `k,n,m` folgt bereits aus der bekannten Zentrum-Null-Konstruktion und dem Anfügen kurzer Blätter mit neuen Maximalwerten. Auch Alpha-Amalgamation und reversible Blattkonstruktion sind bekannte Bausteine.

Mehrere vollständige Teilfamilien des jetzigen Satzes sind älter. Deshalb wäre es falsch, alle inneren Nullpositionen bei `k=5,7,9` pauschal als zusätzliche Abdeckung zu bezeichnen.

| Parameter oder Positionen | Nachgeprüfte ältere Überdeckung | Konsequenz |
|---|---|---|
| Alle `k,n,m`, Zentrum-Null | Wurzelsymmetrische Baumkonstruktion; auch Panpa u. a., Satz 2.4; anschließend kurze Blätter mit neuen Maximalwerten | Grazilität der gesamten Familie ist bekannt |
| `n=2,m=0`, jedes `k` | Bekannte 0-Rotierbarkeit von Pfaden; Luiz–Campos–Richter, Lemma 4; Shan–Zhong, Lemma 2(a,b) | Jeder Knoten ist bereits abgedeckt, auch für `k=9` |
| `n=2,m=1`, jedes `k` | Luiz–Campos–Richter (2017), Satz 14: ein Blatt an einem zentralen Pfadknoten | Jeder Knoten ist bereits abgedeckt |
| `k=3,n=2`, jedes `m` | Luiz–Campos–Richter, Satz 22: sämtliche Caterpillars mit Durchmesser sechs | Jeder Knoten ist bereits abgedeckt |
| `k=3,m=0`, jedes `n` | Rofa, Korollar 3: symmetrische Spinnen mit Beinlänge höchstens drei | Jeder Knoten ist bereits abgedeckt |
| Alle `k,n≥2,m≥0`, Spitzen, ihre Vorgänger und kurze Blätter | Zentrum-Null, Patterson, Satz 5.3.6, und Komplementieren | Diese Positionen folgen aus bekannten Bausteinen; dies ist eine Ableitung, kein wörtlicher Familiensatz der Quelle |
| `k=5,7,9` im übrigen Parameterbereich | Kein vollständiger Satz über jeden vorgeschriebenen Nullknoten in den geprüften Originalquellen gefunden | Mögliche zusätzliche Abdeckung gegenüber diesen Quellen; historische Priorität ungeklärt |

**Patterson (2017).** In der Dissertation wurden Korollar 2.4.3, die Sätze 3.1.3, 3.2.1, 3.3.8 und 5.3.6 sowie Vermutung 5.4.4 geprüft. Sie enthält uniforme Zentrum-Null, Alpha-Amalgamation mit Verweis auf Huang–Kotzig–Rosa (1982), reversible Armblattkonstruktionen und eine ältere Vermutung über Spinnen-0-Rotierbarkeit. Satz 3.3.8 betrifft Grazilität bei höchstens drei Armen länger als eins. Vermutung 5.4.4 schließt die hier betrachteten Familien mit mindestens zwei langen Armen ein, beweist sie aber nicht. Die endliche Erfassung von Bäumen bis Ordnung 16 ist ebenfalls kein Beweis für unbeschränkte Parameter. [Institutioneller Originaltext](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content).

**Luiz–Campos–Richter (2017), Technical Report IC-17-12.** Satz 14 auf gedruckter Seite 6 behandelt einen Pfad mit einem Blatt an einem zentralen Knoten. Satz 22 auf gedruckten Seiten 16–17 behandelt jeden Caterpillar mit Durchmesser sechs. Sie liefern genau die in der Tabelle bezeichneten `n=2`-Überdeckungen. Bei `k=3` verändern zusätzliche Zentrumsblätter den Durchmesser sechs nicht. Die Satzformulierungen wurden im Original geprüft; ein vollständiger Neubeweis der Literaturarbeit wurde nicht erstellt. Satznummern des Berichts dürfen ohne gesonderte Kontrolle nicht auf den verwandten Zeitschriftenartikel von 2020 übertragen werden. [Universitärer Originalbericht](https://ic.unicamp.br/~reltech/2017/17-12.pdf), [Zeitschriftenartikel von 2020](https://doi.org/10.1007/s00373-020-02226-0).

**Rofa (2023).** Satz 1 liefert Wurzel-Null. Korollar 3 auf gedruckter Seite 12 beweist die 0-Rotierbarkeit symmetrischer Spinnen mit Beinlänge höchstens drei. Satz 2 hat Voraussetzungen über Wurzelsymmetrie und einen verbleibenden Caterpillar. Die Arbeit lässt symmetrische Spinnen mit Beinlängen ab vier ausdrücklich offen. Für `k=3,n≥3,m≥1` besitzt die ausgezeichnete Wurzel sowohl Blätter als auch innere Knoten auf der ersten Ebene und ist keine symmetrische Wurzel; Korollar 3 ist daher auf diese gemischte Familie nicht unmittelbar anwendbar. Die uniformen Familien `m=0` gehören zum älteren vermuteten Bereich. [Original-PDF](https://arxiv.org/pdf/2312.16235), [Datensatz](https://arxiv.org/abs/2312.16235).

**Panpa–Imnang–Wasuanankul (2025).** Satz 2.4 wiederholt uniforme Zentrum-Null, Satz 2.5 die hier verwendete Alpha-Amalgamation. Satz 3.2 gibt Zentrum-Null für drei Beine, Satz 3.3 jedes Blatt als Null für vier Beine und Satz 3.4 Grazilität für fünf Beine. Dabei zählen alle Beine. Die spätere Paraphrase „fünf nichttriviale Beine“ darf nicht als verifizierte Originalaussage übernommen werden. Die Sätze liefern keine vollständige innere Nullabdeckung für beliebig viele Arme. [Verlagstext](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777).

**Shan–Zhong (2026), Version 2.** Lemma 1 wiederholt die Alpha-Amalgamation; Lemma 2(a,b) die Pfad-0-Rotierbarkeit. Satz 5 beweist Grazilität, wenn höchstens drei Beine länger als zwei sind, und deckt damit hier `n≤3` ab. Er behauptet keine volle 0-Rotierbarkeit. [Originaltext, Version 2](https://arxiv.org/html/2605.14295v2).

**Bahls–Lake–Wertheim (2010).** Satz 1 liefert Grazilität für Beinlängen aus `{r,r+1}` und umfasst uniforme Spinnen. Die gemischten Beinlängen `{1,k}` für `k≥3` sind nicht unmittelbar enthalten. Die Arbeit erklärt ausdrücklich, dass der Satz aus Poljak–Sura (1982) folgt. Ein vollständiger Satz über vorgeschriebene Nullpositionen steht dort nicht. [Verlags-PDF](https://msp.org/involve/2010/3-3/involve-v3-n3-p01-p.pdf).

**Niu (2026).** Der arXiv-Datensatz bestätigt den Rückzug vom 14. Mai 2026 wegen fehlender Neuheit der uniformen Zentrum-Null-Konstruktion mit routinemäßiger Blatterweiterung. Version 1 betraf gewöhnliche Grazilität von Drei-Kanten-Armen mit Zentrumsblättern. Die verbleibende Neuheitsformulierung im Abstract wird hier nicht übernommen. [Originaler Rückzugsvermerk](https://arxiv.org/abs/2605.02303).

In den geprüften Primärquellen wurde der vollständige Zweiparametersatz für `k=5,7,9` nicht gefunden. Das begründet keine Neuheits- oder Erstbeweisbehauptung. Alle vier Familien liegen im Bereich älterer Vermutungen. Die Originalvolltexte von 1977 und 1982, Cattells vollständige Klassifikation gleichzeitig vorgeschriebener Pfadlabels sowie die rückwärts und vorwärts verlaufenden Zitationsketten wurden nicht erschöpfend geprüft. Ältere Pfadtabellen oder allgemeinere labelerhaltende Kompositionssätze könnten die Zertifikate bereits umfassen. Historische Priorität bleibt offen.

## 10. KI-Beiträge und Grenzen der Prüfung

KI-Unterstützung wurde bei der deterministischen Suche nach Alpha-Pfad-Zeugen, der Entwicklung und Formulierung des Kompositionsbeweises, der Ableitung und Prüfung der expliziten Formeln, der Programmierung von Konstruktion und Prüfern, der Literaturabgrenzung und der Textvorbereitung eingesetzt. Die sechs numerischen Zeugen sind Ergebnisse einer programmierten Suche; ihre Gültigkeit folgt aus den angegebenen Labels und Differenzen. Die Suchzahlen sind keine Beweisargumente.

Die erste Konstruktion und der erste Prüfer entstanden in derselben Sitzung. Eine getrennte interne Agentenprüfung verwendete anschließend eine eigene Implementierung und prüfte den schriftlichen Beweis. „Intern unabhängig“ bezeichnet hier die getrennte Durchführung und Programmierung. Es bezeichnet keine Begutachtung durch einen externen Mathematiker. Auch die Literaturprüfung ist eine gezielte interne Quellenprüfung und keine abgeschlossene Prioritätsuntersuchung. Die deutsche Fassung ist ein KI-unterstützter Übersetzungsentwurf und wurde noch nicht von einem Menschen sprachlich geprüft.

Eine genaue nächste mathematische Frage lautet: Existiert für jedes ungerade `k≥3` und jede gerade Tiefe `d` mit `2≤d≤k−3` ein Alpha-Pfad der oben beschriebenen Art mit Null in Tiefe `d`, Maximum in Tiefe `d+1` und Mittelpunkt an der Alpha-Schwelle? Eine allgemeine Konstruktion dafür würde zusammen mit den Abschnitten 2–5 die 0-Rotierbarkeit für alle ungeraden `k`, `n≥2` und `m≥0` beweisen. Eine solche allgemeine Konstruktion wird hier nicht bewiesen.

Der belegte Umfang dieser Notiz ist ein expliziter, intern getrennt nachgerechneter Zertifikat-und-Kompositionsbeweis für die vier genannten Familien, mit bekannten Bausteinen und bekannten Randfamilien. Externe Fachprüfung und eine vollständige historische Prioritätsprüfung stehen aus.





