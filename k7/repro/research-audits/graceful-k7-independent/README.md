# Unabhängige Gegenprüfung der 0-Rotierbarkeit von S(7,7,7,1^m)

**GO für die mathematische Aussage:** Für jedes ganze `m>=1` ist `S(7,7,7,1^m)` vollständig 0-rotierbar. Die fünf direkt gegebenen Basiszeilen und vier Komplemente erfüllen die benötigte Schwelleninvariante. Das Einfügelemma schließt jedes `m>=1` ein. Eine Behauptung wissenschaftlicher Neuheit ist mit diesem Urteil nicht verbunden.

Prüfstand: 8. Oktober 2026. Die Ausgangsdateien in `../graceful-k7-feasibility/` wurden ausschließlich gelesen. [independent_check.py](independent_check.py) importiert oder startet keinen ursprünglichen Prüfer und keinen Suchcode. [audit-results.json](audit-results.json) enthält Eingabeprüfsummen, die vollständigen Kanten- und Labeldaten aller neun Zeilen sowie exakte affine Kantenzertifikate.

## Kanten und neun Nullpositionen

Der neue Prüfer erzeugt einen Baum aus den Beinlängen `[7,7,7,1,...,1]`. Das Zentrum hat Knotennummer 0, die drei langen Arme erhalten die Knotennummern 1 bis 7, 8 bis 14 und 15 bis 21; die kurzen Blätter erhalten 22 bis `21+m`. Innerhalb jedes langen Arms werden aufeinanderfolgende Knoten verbunden, und der erste Knoten jedes Beins wird mit dem Zentrum verbunden. Die Kantenmenge enthält genau `21+m` verschiedene Kanten; der Graph ist zusammenhängend und hat genau `22+m` Knoten.

Für jede Basiszeile wurden die Knotenlabels als Multimenge mit `0,...,22` und sämtliche 22 einzeln rekonstruierten Kantendifferenzen als Multimenge mit `1,...,22` verglichen. Damit sind sowohl Auslassungen als auch Mehrfachverwendungen ausgeschlossen.

| Nullposition | Zentrum c | Schwelle t | d | gleiche Seite | querende Kanten |
| --- | ---: | ---: | ---: | --- | --- |
| Zentrum | 0 | 21 | 22 | 1 bis 21 | 22 |
| Armtiefe 1 | 20 | 2 | 18 | 1 bis 17 | 18 bis 22 |
| Armtiefe 2 | 2 | 19 | 18 | 1 bis 17 | 18 bis 22 |
| Armtiefe 3 | 20 | 1 | 19 | 1 bis 18 | 19 bis 22 |
| Armtiefe 4 | 2 | 20 | 19 | 1 bis 18 | 19 bis 22 |
| Armtiefe 5 | 19 | 2 | 17 | 1 bis 16 | 17 bis 22 |
| Armtiefe 6 | 3 | 19 | 17 | 1 bis 16 | 17 bis 22 |
| Armtiefe 7 | 19 | 3 | 16 | 1 bis 15 | 16 bis 22 |
| kurzes Blatt | 22 | 0 | 22 | 1 bis 21 | 22 |

Das Zentrum ist für jedes `m>=1` der einzige Knoten vom Grad größer als zwei und wird daher von jedem Automorphismus festgehalten. Der Abstand zum Zentrum unterscheidet die sieben langen Armtiefen. In Tiefe eins unterscheiden die Grade zwei und eins die langen Arme von den kurzen Blättern. Beliebige Vertauschungen der drei langen Arme sowie der kurzen Blätter sind Automorphismen. Folglich bestehen genau die neun tabellierten Orbits. Eine Beschriftung je Orbit lässt sich auf jeden gewünschten Knoten dieses Orbits übertragen.

## Einfügelemma für beliebig viele Blätter

Sei ein Baum mit `q` Kanten durch eine Bijektion `b` auf `0,...,q` grazil beschriftet. An einem ausgezeichneten Knoten mit Label `c` sollen neue Blätter entstehen. Sei `0<=t<=q` ganzzahlig und

`d=c-t` für `c>t`, andernfalls `d=t+1-c`.

Vorausgesetzt wird, dass die Kantendifferenzen auf derselben Seite der Schwelle genau `1,...,d-1` sind und die querenden Kantendifferenzen genau `d,...,q`, jeweils mit Vielfachheit eins. Diese Voraussetzung ist wesentlich; Grazilität allein reicht für die folgende Konstruktion nicht aus.

Für ein beliebiges ganzzahliges `n>=0` erhöhe alle alten Labels größer als `t` um `n`. Gib den `n` neuen Blättern die Labels `t+s`, `1<=s<=n`. Die drei Labelblöcke sind dann

`[0,t]`, `[t+1,t+n]`, `[t+n+1,q+n]`.

Leere Intervalle werden ausgelassen. Die Blöcke sind disjunkt und ergeben genau `0,...,q+n`. Die ursprüngliche Null bleibt erhalten, weil `t>=0`, und kein neues Blatt erhält Null.

Eine alte gleichseitige Kante behält ihre Differenz. Eine alte querende Kante erhält ihre ursprüngliche Differenz plus `n`; das höhere Ende bleibt das höhere Ende. Deshalb liefern die alten Kanten genau die Intervalle

`[1,d-1]` und `[d+n,q+n]`.

Für hohes Zentrum ist die neue Kantendifferenz `(c+n)-(t+s)=d+n-s`. Für niedriges Zentrum ist sie `(t+s)-c=d+s-1`. Beide Ausdrücke sind positiv und durchlaufen bei `1<=s<=n` genau das fehlende Intervall `[d,d+n-1]`. Die drei Differenzblöcke sind somit disjunkt und ergeben genau `1,...,q+n`.

Dies beweist die Erweiterung für jedes `n>=0`. Bei hohem Zentrum wird der Parameter der fortgesetzten Schwelleninvariante `d+n`; bei niedrigem Zentrum bleibt er `d`. Die Invariante besteht also auch nach der Einfügung. Mit `q=22` und `n=m-1` folgt der Hauptsatz für jedes `m>=1`, einschließlich `m=1`, bei dem keine neue Kante entsteht.

Die Formel in `continuation.md` nummeriert die neuen Blätter in umgekehrter Reihenfolge: `p_j` erhält `t+m-j`. Das entspricht hier `s=m-j` und verändert dieselbe Kantenmultimenge. Der Checker vergleicht diese konkrete Nummerierung außerdem mit zwölf aufeinanderfolgenden Einfügungsständen.

## Komplementierung und ihr Randfall

Für `b'(v)=q-b(v)` und `t'=q-1-t` werden die Schwellen-Seiten vertauscht. Die Kantendifferenzen bleiben erhalten. Ist `c>t`, dann liegt `c'=q-c` unterhalb oder auf `t'`, und `t'+1-c'=c-t=d`. Ist `c<=t`, dann liegt `c'>t'`, und `c'-t'=t+1-c=d`. Der Parameter und beide Differenzintervalle bleiben somit erhalten.

Für eine anschließende Einfügung, die die neue Null erhält, genügt der genaue Bereich `0<=t<=q-1`, denn dann gilt ebenfalls `0<=t'<=q-1`. Sämtliche verwendeten Basiszeilen erfüllen diesen Bereich. Bei `t=q` wäre `t'=-1`; eine pauschale Behauptung, dass Komplementierung im ganzen Bereich `0<=t<=q` die nullerhaltende Invariante liefert, wäre zu weit. Die vorliegenden Beweise behaupten oder benötigen diesen Randfall nicht. Das Einfügelemma selbst bleibt bei `t=q` gültig.

## Ungerade Armspitzen und der Drei-Bein-Satz

Das bedingte Reduktionslemma ist korrekt, einschließlich `k=1`. Schreibe `k=2r+1`, `r>=0`. Eine grazile Beschriftung von `S(k,k,1)` hat `4r+3` Kanten. Liegt ihr Zentrum auf `4r+3`, erzeugt eine Verschiebung aller Labels um `r+1` genau das Intervall `[r+1,5r+4]` und Zentrum `5r+4`.

Setze `q=6r+4`. Am neuen Arm sei das Label in Tiefe `2i+1` gleich `r-i` für `0<=i<=r`, in Tiefe `2i+2` gleich `q-r+1+i` für `0<=i<r`. Dies belegt genau `[0,r]` und `[5r+5,6r+4]`. In Tiefe `j`, `1<=j<=2r+1`, beträgt die Differenz zur vorhergehenden Tiefe, beziehungsweise zum Zentrum, genau `4r+3+j`. Damit liefern die neuen Armkanten `4r+4,...,6r+4`; die alten Kanten behalten `1,...,4r+3`. Mit Schwelle `t=r` und `d=4r+4` ist die Einfügeinvariante erfüllt, und die Spitze hat Label Null.

Das gegebene reduzierte Zertifikat für `k=7` ist selbst grazil und wird nach Verschiebung und Ergänzung exakt zur angegebenen Tiefe-7-Zeile. Für `k=1` kann man separat mit dem Sternzentrum 3 und den Blättern 0, 1, 2 beginnen. Die Konstruktion erzeugt das Zentrum 4 mit vier Blättern 0, 1, 2, 3 und erfüllt `t=0,d=4`; die Fortsetzung funktioniert ebenfalls.

Theorem 3.2 von Panpa, Imnang und Wasuanankul besagt für jeden Drei-Bein-Spider die Existenz einer grazilen Beschriftung mit Zentrum Null. Der geprüfte Originalsatz hat keine weitere Beinlängenvoraussetzung. Komplementierung auf `S(k,k,1)` liefert daher das Zentrum `2k+1`, das die Reduktion voraussetzt. **Als eigene Folgerung** besitzen somit alle `S(k,k,k,1^m)` mit ungeradem `k>=3` und `m>=1` eine grazile Beschriftung mit Null an einer langen Armspitze. Für diese `k` sitzt das Maximum der Basisbeschriftung in Tiefe `k-1`, sodass Komplementierung und Einfügung zusätzlich diese Tiefe abdecken. Dies ist keine Behauptung vollständiger 0-Rotierbarkeit für allgemeines `k`. [Originalsatz und Beweis, Abschnitt 3](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777).

## Schnittidentität und Reproduktion

Bei hohem Zentrum liegen alle `L=t+1` niedrigen Knoten außerhalb des Zentrums. Sind darunter `ell` Blätter und gibt es `e` Kanten mit zwei niedrigen Endpunkten, ist die Summe ihrer Grade `2L-ell`. Genau `2e` davon gehören zu inneren Kanten. Der Schnitt hat deshalb `2L-ell-2e` Kanten. Die Invariante verlangt `q-d+1=q-c+L` Schnittkanten. Gleichsetzen ergibt exakt `q-c=L-ell-2e`.

Bei Null an einer Armspitze gilt `ell>=1`, also `c>=q-t`. Somit sind `q=22,t=2,c=19` für diese Invariante unmöglich: Die niedrigen Knoten können höchstens fünf Schnittkanten tragen, erforderlich wären sechs. Die Behauptung ist korrekt und beschränkt sich auf die genannte Invariante.

Reproduktion aus dem Repository:

```powershell
python research-audits/graceful-k7-independent/independent_check.py
```

Ergebnis des unabhängigen Laufs:

- Neun Basiszeilen mit vollständigen Knoten- und Kantenmultimengen sowie exakten affinen Formeln bestanden.
- 54 explizite Erweiterungen bei `m=1,2,3,8,64,257` bestanden.
- Bei `m=1,2,5` bestanden alle 74 expliziten Transporte der Null auf jeden einzelnen Knoten; die erzeugenden Permutationen erhielten die Kantenmenge.
- Unter allen 5.913 möglichen Differenzkanten-Auswahlen für `q=1,...,7` lagen 975 grazile Bäume. Für sämtliche ausgezeichneten Knoten und Schwellen erfüllten 6.189 Konfigurationen die Invariante. Alle 18.567 daraus geprüften Einfügungen von 1, 2 oder 5 Blättern bestanden, ebenso 5.214 zulässige Komplementierungen. Darunter lagen auch 975 Fälle mit `t=q`.
- Reduziertes Zertifikat, separater Grenzfall `k=1`, Armindexformeln, Schnittidentität und ein absichtlich falscher Schwellenwert als Negativkontrolle bestanden.

Die endlichen Prüfungen stützen die Implementierung. Die unbeschränkte Aussage folgt aus den exakten Label- und Differenzintervallen im Einfügebeweis. Es wurde keine fehlende Größe `m>=1` und kein Fehler in den für den Hauptsatz benötigten Voraussetzungen gefunden. `m=0`, allgemeine Armlängen und wissenschaftliche Priorität sind vom GO nicht umfasst.
