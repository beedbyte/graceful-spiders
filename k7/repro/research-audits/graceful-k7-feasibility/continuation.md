# Interner Beweis für S(7,7,7,1^m)

**Status (2026-10-08): Alle neun Null-Label-Orbits sind für jedes ganze m>=1 bewiesen.** Die vier neuen Basiszertifikate wurden mit einem unabhängig implementierten Python-Prüfer bestätigt. Der Bericht enthält keine Behauptung über wissenschaftliche Neuheit oder Publikationspriorität. Keine Veröffentlichung oder Änderung an der Website wurde vorgenommen.

## Satz und neue Basiszertifikate

Für jedes ganze `m>=1` ist `S(7,7,7,1^m)` 0-rotierbar. Der Baum besteht aus einem Zentrum, drei Armen mit je sieben Kanten und `m` weiteren Zentrumsblättern. Er hat `q=21+m` Kanten. Zu jedem vorgegebenen Knoten existiert eine bijektive Beschriftung mit `0,...,q`, die diesem Knoten `0` zuweist und jede Kantendifferenz `1,...,q` genau einmal verwendet.

Die vier neuen Zeilen gelten bei `m=1`, also `q=22`. Armfolgen laufen vom Zentrum nach außen. `t` bezeichnet die Schwelle und hier jeweils `d=c-t`.

| Null-Orbit | Zentrum c | Arm 0 | Arm 1 | Arm 2 | Zentrumsblatt | t | d |
| --- | ---: | --- | --- | --- | ---: | ---: | ---: |
| Armtiefe 1 | 20 | (0,22,1,19,3,17,9) | (8,14,13,6,4,21,2) | (5,18,7,16,11,15,12) | 10 | 2 | 18 |
| Armtiefe 3 | 20 | (2,19,0,22,1,21,5) | (6,3,18,7,9,14,13) | (10,16,4,17,8,15,11) | 12 | 1 | 19 |
| Armtiefe 5 | 19 | (2,20,1,21,0,22,6) | (4,3,15,9,14,11,13) | (5,18,10,17,7,16,12) | 8 | 2 | 17 |
| Armtiefe 7 | 19 | (3,20,2,21,1,22,0) | (4,7,16,8,14,12,13) | (5,18,6,17,10,15,11) | 9 | 3 | 16 |

Die jeweiligen Kantendifferenzen sind:

| Null-Orbit | Arm 0 | Arm 1 | Arm 2 | Blattkante |
| --- | --- | --- | --- | ---: |
| Armtiefe 1 | (20,22,21,18,16,14,8) | (12,6,1,7,2,17,19) | (15,13,11,9,5,4,3) | 10 |
| Armtiefe 3 | (18,17,19,22,21,20,16) | (14,3,15,11,2,5,1) | (10,6,12,13,9,7,4) | 8 |
| Armtiefe 5 | (17,18,19,20,21,22,16) | (15,1,12,6,5,3,2) | (14,13,8,7,10,9,4) | 11 |
| Armtiefe 7 | (16,17,18,19,20,21,22) | (15,3,9,8,6,2,1) | (14,13,12,11,7,5,4) | 10 |

Jede Zeile enthält sämtliche Knotenlabels `0,...,22` und sämtliche Kantendifferenzen `1,...,22` jeweils einmal. In jeder Zeile sind die Differenzen auf derselben Schwellen-Seite genau `1,...,d-1`, die Differenzen über die Schwelle genau `d,...,22`.

Die Transformation `f -> 22-f`, `t -> 21-t` vertauscht die Schwellen-Seiten, erhält aber alle Kantendifferenzen und den Parameter `d`. In den ersten drei Zeilen liegt `22` in Tiefe 2, 4 beziehungsweise 6. Ihre Komplemente liefern daher die drei weiteren Null-Orbits, mit Schwellen 19, 20 und 19. Die beiden alten Zertifikate für Zentrum und Zentrumsblatt in `bases.json` vervollständigen die neun Orbits.

## Beweis für beliebiges m

Sei `b` eine der neun Basisbeschriftungen mit Schwelle `t`. Für die alten Knoten definiere direkt

`f_m(v) = b(v)` bei `b(v)<=t`, sonst `f_m(v)=b(v)+m-1`.

Für die neuen Zentrumsblätter `p_j`, `1<=j<=m-1`, setze

`f_m(p_j)=t+m-j`.

Die alten niedrigen Labels belegen `0,...,t`, die neuen Blätter `t+1,...,t+m-1`, und die alten hohen Labels `t+m,...,m+21`. Das ist die erforderliche Bijektion. Das ursprüngliche Null-Label bleibt erhalten.

Alte gleichseitige Kantendifferenzen bleiben `1,...,d-1`. Alte querende Differenzen werden um `m-1` erhöht und bilden `d+m-1,...,m+21`. Liegt das Basiszentrum oberhalb der Schwelle, hat die neue Kante zu `p_j` die Differenz `d+j-1`; liegt es unterhalb oder auf der Schwelle, ist die Differenz `d+m-j-1`. In beiden Fällen liefern die neuen Blattkanten genau `d,...,d+m-2`, mit leerem Intervall für `m=1`. Die drei Intervalle sind disjunkt und ergeben genau `1,...,m+21`. Das beweist die Behauptung für alle `m>=1` ohne Extrapolation aus endlich vielen Tests.

Die drei langen Arme sind untereinander vertauschbar; ebenso die Zentrumsblätter. Die neun Orbits Zentrum, Armtiefen 1 bis 7 und Zentrumsblatt decken jeden Knoten ab. Damit ist der Satz bewiesen.

## Reduktion für die Armspitze bei ungerader Armlänge

**Hinreichendes Reduktionslemma.** Sei `k=2r+1` ungerade, `r>=0`. Hat `S(k,k,1)` eine grazile Beschriftung mit Zentrum `2k+1=4r+3`, dann besitzt `S(k,k,k,1^m)` für jedes `m>=1` eine grazile Beschriftung mit Null an einer langen Armspitze.

Beweis: Bei `m=1` setze `q=3k+1=6r+4`. Erhöhe sämtliche Labels der gegebenen Beschriftung um `r+1`; sie belegen dann das Intervall `r+1,...,5r+4`, das Zentrum erhält `5r+4`. Füge am Zentrum einen Arm der Länge `2r+1` mit der alternierenden Folge

`r, q-r+1, r-1, q-r+2, ..., 1, q, 0`

hinzu. Präzise lautet das Label in Tiefe `2i+1` gleich `r-i` für `0<=i<=r`; in Tiefe `2i+2` gleich `q-r+1+i` für `0<=i<r`. Diese Labels sind genau `0,...,r` und `5r+5,...,6r+4`. Die neuen Armkanten haben der Reihe nach die Differenzen `4r+4,...,6r+4`. Die alten Kanten behalten `1,...,4r+3`. Mit Schwelle `t=r` liegen alle alten Kanten auf der hohen Seite und alle neuen Armkanten über der Schwelle. Der Parameter ist `d=(5r+4)-r=4r+4`. Somit gilt die Einfügeinvariante und der Schluss für jedes `m>=1`.

Für `k=7` liefert das reduzierte Zertifikat Zentrum 15, Arme `(0,3,12,4,10,8,9)` und `(1,14,2,13,6,11,7)` sowie Zentrumsblatt 5 eine solche Beschriftung von `S(7,7,1)`. Verschiebung um 4 liefert exakt die vierte Tabellenzeile. Das Lemma ist eine hinreichende Reduktion; hier wird keine universelle Existenz des benötigten reduzierten Zertifikats für alle ungeraden `k` behauptet.

## Exakte Schnitt-Obstruktion für Suchparameter

Für eine beliebige Schwellenbeschriftung eines Spiders `S(k,k,k,1^m)` mit hohem Zentrum `c>t`, `k>=2`, sei `L=t+1`, `ell` die Anzahl seiner Blätter unter den niedrigen Labels und `e` die Anzahl der Kanten mit zwei niedrigen Endpunkten. Alle niedrigen Knoten liegen außerhalb des Zentrums, haben also Grad 2 oder als Blätter Grad 1. Daher hat der Schnitt genau `2L-ell-2e` Kanten. Die Invariante fordert hingegen `q-d+1=q-c+L` querende Kanten. Also gilt notwendig

`q-c = L-ell-2e`.

Insbesondere verlangt ein Null-Label an einer Armspitze `ell>=1` und daher `c>=q-t`. Bei `q=22`, `t=2`, `c=19` ist das unmöglich: Drei niedrige Knoten, darunter die Null-Armspitze, können höchstens fünf Schnittkanten tragen, während die Invariante sechs verlangt. Der frühere tiefe Suchlauf für `arm7 50000000 50000000 2 19` war somit in einem unmöglichen Parameterpaar. Diese Aussage betrifft ausschließlich die Schwelleninvariante, nicht beliebige grazile Beschriftungen oder 0-Rotierbarkeit.

Für den neuen Tiefe-1-Treffer `t=2,c=20` fordert die Identität `ell+2e=1`: genau ein niedriges Blatt und keine niedrig-niedrig-Kante. Das motiviert die Vorlage mit Label 2 an einer anderen Armspitze, benachbart zu Label 21. Für Tiefe 7 mit `t=3,c=19` ergibt sich derselbe Defekt 1, den die niedrige Null-Armspitze erfüllt.

## Reproduktion und Grenzen

Die neuen Zeilen stehen in `continuation-bases.json`. Der neue Standardbibliotheks-Prüfer importiert keinen Suchcode und keinen älteren Checker. Er kontrolliert die neun Basiszeilen, die einzelnen Kantendifferenzen einschließlich ihrer Vielfachheit, die Null-Orbits, beide Schwellenintervalle, exakte affine Formeln für die alten Kanten, die Schnittidentität, das reduzierte Zertifikat und 900 explizite Beschriftungen für `m=1,...,100`.

```powershell
python research-audits/graceful-k7-feasibility/verify-continuation.py
node research-audits/graceful-k7-feasibility/arm1-template-search.js 100000000
node research-audits/graceful-k7-feasibility/arm-template-search.js arm3 100000000
node research-audits/graceful-k7-feasibility/arm-template-search.js arm5 100000000
node research-audits/graceful-k7-feasibility/tip-reduction-search.js 7 100000000
```

Der Prüfer meldet `9 of 9 zero-label orbits verified; reduced tip witness PASS.` sowie die bestätigte Schnitt-Obstruktion. Die Suchläufe liefern in obiger Reihenfolge Zeugen nach 13.752.278, 1.962.854, 1.548.663 und 4.938.764 DFS-Eintritten. Diese Knotenstände sind Reproduktionsdaten der konkreten Vorlagen. Ein ausgeschöpftes Budget wäre `UNKNOWN`; eine vollständig ausgeschöpfte Vorlage würde nur diese Vorlage ausschließen.

Die unbeschränkte Aussage betrifft nur `S(7,7,7,1^m)` für `m>=1`. Für `m=0`, andere Anzahlen langer Arme oder allgemeine Armlängen wird kein Satz behauptet. Die Neuheit gegenüber der Fachliteratur und eine externe unabhängige mathematische Begutachtung bleiben offen.
