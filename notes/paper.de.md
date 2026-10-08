**Forschungsnotiz · Version 1 · 8. Oktober 2026**

Diese Notiz gehört zum Projekt [Drei gleich lange Arme: 0-Rotierbarkeit bei Längen drei und vier](https://beedbyte.tech/de/research/graceful-spider-three-arms).

## Aussage und Begriffe

Für `k` gleich 3 oder 4 und jede ganze Zahl `m >= 1` sei `S_(k,m)=S(k,k,k,1^m)` der Baum mit Mittelpunkt `c`, drei langen Armen `a_i1,...,a_ik` für `i=0,1,2` (vom Mittelpunkt nach außen) und `m` weiteren, direkt an `c` hängenden Blättern `p_0,...,p_(m-1)`. Er hat `q=3k+m` Kanten. Eine grazile Beschriftung ist eine Bijektion der Knoten auf `{0,...,q}`, deren Kantendifferenzen genau `{1,...,q}` sind.

**Sätze A und B.** Für jedes `k` aus `{3,4}` und jedes ganzzahlige `m >= 1` ist `S_(k,m)` 0-rotierbar: Zu jedem vorgegebenen Knoten `v` gibt es eine grazile Beschriftung mit `f(v)=0`. Über andere Werte von `k` wird nichts behauptet.

## Satz A: fünf Grundzertifikate für Armlänge drei

Für `k=3` und `m=1` enthält die Tabelle je eine Beschriftung für jede Knotenklasse unter den Symmetrien des Baums. Jedes Armtripel nennt die Beschriftungen in den Tiefen 1, 2 und 3. `t` ist die unten verwendete feste Einfügeschwelle; `d` ist die Differenz der Kante zum nächsten eingefügten Blatt.

| Knoten mit Null | `c` | Arm 0 | Arm 1 | Arm 2 | `p_0` | `t` | `d` |
| --- | ---: | --- | --- | --- | ---: | ---: | ---: |
| Mittelpunkt | 0 | (1,6,4) | (8,2,5) | (10,3,7) | 9 | 10 | 11 |
| Arm, Tiefe 1 | 8 | (0,10,1) | (2,9,4) | (6,7,3) | 5 | 2 | 6 |
| Arm, Tiefe 2 | 1 | (9,0,10) | (4,3,5) | (7,2,6) | 8 | 7 | 7 |
| Arm, Tiefe 3 | 9 | (1,10,0) | (2,5,6) | (3,8,4) | 7 | 1 | 8 |
| Blatt am Mittelpunkt | 10 | (1,3,8) | (2,9,5) | (4,7,6) | 0 | 0 | 10 |

Jede Zeile benutzt die Knotenbeschriftungen `0,...,10` genau einmal. Eine Kante heißt *gleichseitig*, wenn beide Endpunkte Beschriftungen höchstens `t` oder beide Beschriftungen größer als `t` tragen; andernfalls heißt sie *querend*. Direktes Nachrechnen liefert die folgenden **disjunkten** Intervalle. Innerhalb jedes Intervalls tritt jede Differenz genau einmal auf.

| Null-Klasse | Gleichseitige Differenzen | Querende Differenzen |
| --- | --- | --- |
| Mittelpunkt | 1,...,10 | leer |
| Arm, Tiefe 1 | 1,...,5 | 6,...,10 |
| Arm, Tiefe 2 | 1,...,6 | 7,...,10 |
| Arm, Tiefe 3 | 1,...,7 | 8,...,10 |
| Blatt am Mittelpunkt | 1,...,9 | 10 |

Damit ist jede Zeile grazil. Der exakte Prüfer und das unabhängige Audit im Paket prüfen alle einzelnen Kanten als sortierte Listen; eine Mengenprüfung allein könnte doppelte Differenzen verdecken.

## Gemeinsames Schwellen-Einfügelemma

Ein Baum `T` habe `q` Kanten, eine grazile Beschriftung `f`, einen Knoten `c`, an dem ein Blatt ergänzt werden soll, und eine feste ganze Zahl `0 <= t <= q`. Setze

`d=t+1-f(c)`, falls `f(c)<=t`, und `d=f(c)-t`, falls `f(c)>t`.

Vorausgesetzt sei, dass die gleichseitigen Kanten genau einmal die Differenzen `1,...,d-1` und die querenden Kanten genau einmal `d,...,q` tragen. Ergänze ein neues Blatt an `c`, erhöhe jede alte Beschriftung über `t` um eins und gib dem neuen Blatt `t+1`:

`f+(v)=f(v)+1_[f(v)>t]` für alte Knoten; `f+(neues Blatt)=t+1`.

Die alten Beschriftungen werden zu `0,...,t,t+2,...,q+1`; das neue Blatt füllt die einzige Lücke. Alte gleichseitige Differenzen bleiben gleich. Jede alte querende Differenz wächst um eins. Die neue Blattkante hat Differenz `d`. Damit entstehen genau einmal die Differenzen `1,...,d-1`, `d` und `d+1,...,q+1`.

Auch die Intervallvoraussetzung bleibt bei **derselben Schwelle `t`** erhalten:

1. Ist `f(c)<=t`, bleibt der Mittelpunkt auf der unteren Seite und das neue Blatt liegt oben. Seine Kante ist querend mit Differenz `d`. Das gleichseitige Intervall bleibt `1,...,d-1`; die alten querenden Differenzen werden `d+1,...,q+1`. Zusammen mit der neuen Kante ist das querende Intervall `d,...,q+1`. Der Parameter `d` ändert sich nicht.
2. Ist `f(c)>t`, steigt die Mittelpunktbeschriftung um eins; Mittelpunkt und neues Blatt liegen beide oben. Ihre Kante ist gleichseitig mit Differenz `d`. Der neue Parameter ist `d'=d+1`. Das gleichseitige Intervall ist `1,...,d` (also `1,...,d'-1`), das querende Intervall ist `d'=d+1,...,q+1`.

Das Invariant lässt sich also beliebig oft fortsetzen. Die Null bleibt am bisherigen Knoten: `0` ist nie größer als `t`, und das neue Blatt erhält die positive Beschriftung `t+1`.

Wende das Lemma wiederholt auf jede der fünf Zeilen für Armlänge drei an. Sie decken den Mittelpunkt, alle drei Tiefen eines langen Arms und ein kurzes Blatt ab. Durch Vertauschen der langen Arme oder der kurzen Blätter lässt sich jeder vorgegebene Knoten auf den passenden Null-Vertreter abbilden. Damit gilt Satz A für alle `m >= 1`.

## Satz B: sechs Grundzertifikate für Armlänge vier

Für `k=4` gilt dasselbe Lemma mit sechs anderen Grundzeilen bei `m=1` und `q=13`. Jedes Armquartett nennt die Knotenbeschriftungen in den Tiefen 1 bis 4. Jede Zeile verwendet `0,...,13` und die Kantendifferenzen `1,...,13` jeweils genau einmal. Die letzten beiden Spalten geben die feste Schwelle und die Differenz der nächsten Blattkante an.

| Knoten mit Null | `c` | Arm 0 | Arm 1 | Arm 2 | `p_0` | `t` | `d` |
| --- | ---: | --- | --- | --- | ---: | ---: | ---: |
| Mittelpunkt | 0 | (1,8,3,7) | (12,4,6,9) | (13,2,11,5) | 10 | 13 | 14 |
| Arm, Tiefe 1 | 10 | (0,13,1,12) | (2,11,4,5) | (6,8,3,9) | 7 | 2 | 8 |
| Arm, Tiefe 2 | 1 | (12,0,13,3) | (7,2,6,5) | (10,8,11,4) | 9 | 7 | 7 |
| Arm, Tiefe 3 | 11 | (1,12,0,13) | (2,5,6,8) | (3,10,4,9) | 7 | 1 | 10 |
| Arm, Tiefe 4 | 2 | (12,1,13,0) | (8,4,9,7) | (10,3,6,5) | 11 | 4 | 3 |
| Blatt am Mittelpunkt | 13 | (1,3,11,6) | (2,12,5,9) | (4,10,7,8) | 0 | 0 | 13 |

Die gleichseitigen Differenzen dieser Zeilen sind der Reihe nach `1,...,13`, `1,...,7`, `1,...,6`, `1,...,9`, `1,...,2` und `1,...,12`. Die querenden Differenzen bilden jeweils das ergänzende zusammenhängende Intervall `d,...,13` (in der Mittelpunktzeile leer). Jede einzelne Differenz kommt genau einmal vor; das bestätigen `k4_bases.json`, `k4_verify.py` und das gesonderte `audit-k4.md`.

Das Lemma erweitert somit alle sechs Zeilen mit unveränderter Schwelle auf jedes `m >= 1`; die Null bleibt am ursprünglichen Knoten. Die sechs Knotenklassen sind Mittelpunkt, Armtiefen 1 bis 4 und ein kurzes Blatt. Symmetrien der Arme und der kurzen Blätter decken jeden vorgegebenen Knoten ab. Damit ist Satz B bewiesen.

## Reproduktion und Prüfung

Die herunterladbare Datei `graceful-spider-three-arms-proof.zip` enthält beide Grunddatensätze, beide exakten Prüfer (`verify_proof.py` und `k4_verify.py`), begrenzte Suchprogramme, beide unabhängigen internen Audits (`audit.md` und `audit-k4.md`), die ursprünglichen Beweisnotizen, die Literaturübersicht und `BUNDLE-README.md`. Ihr SHA-256 lautet `86b4e0f5c01a8f43a4579894e891a3ef362c675280ca70a75b9df790b064b549`. Nach dem Entpacken können `python verify_proof.py` und `python k4_verify.py` ausgeführt werden. Mit Python 3.12.1 wurden am 8. Oktober 2026 alle Grundzeilen und das Intervallinvariant für beide Familien bis `m=100` geprüft. Die unbeschränkten Sätze folgen aus dem geschriebenen Lemma und den vollständigen Klassenlisten, nicht aus diesen endlichen Läufen.

Zwei unabhängige interne KI-Audits rekonstruierten die Grundfälle, ohne die jeweiligen Projektprüfer zu importieren, und prüften weitere endliche Invariant-Fälle. Beide melden PASS für die mathematischen Konstruktionen in ihrem genauen Geltungsbereich. Die Beweise sind elementare schriftliche Beweise mit rechnerisch geprüften Zertifikaten; sie wurden weder in einem Beweisassistenten formalisiert noch extern oder durch Peer Review begutachtet. Einige Quelldateien enthalten noch Sätze über ihren historischen Pilotstatus; `BUNDLE-README.md` ordnet diese zeitlich ein.

## Vorarbeiten und Priorität

Pattersons Masterarbeit von 2017 formulierte eine breitere Vermutung zur 0-Rotierbarkeit von Spinnenbäumen (Conjecture 5.4.4) mit einer Ausnahmefamilie. Ihre berichtete endliche Bestandsaufnahme umfasst einige kleine Fälle beider hier behandelten Familien, beweist aber keine Aussage für alle `m`. Das vollständige PDF konnte in dieser Prüfung nicht Seite für Seite untersucht werden; vor einer Einreichung mit Originalitätsanspruch muss der genaue Wortlaut anhand des Originals geprüft werden. Rofas Ergebnis von 2023 betrifft wurzelsymmetrische Bäume und Spinnenbäume mit gleich langen Armen, nicht unmittelbar diese gemischt langen Familien für alle `m`. Bahls, Lake und Wertheim bewiesen Graziliät verwandter Spinnenbäume; Graziliät ist schwächer als 0-Rotierbarkeit. Eine verwandte Idee des Einfügens einer Beschriftungslücke wurde schon früher öffentlich beschrieben; für die allgemeine Idee wird keine Neuheit beansprucht.

Die gezielte Literaturübersicht fand keinen der beiden exakten Sätze für alle `m`. **Die Priorität bleibt ungeklärt; diese Notiz beansprucht weder eine neue Vermutung noch den ersten Beweis oder weltweite Neuheit.** Beide Sätze gelten nur für die genannten Familien mit langen Armen der Länge drei oder vier.
