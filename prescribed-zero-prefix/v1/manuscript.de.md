# D8: geschlossene Nulltiefen-Lücken bei gleichlangen Spider-Armen

**Beedbyte — technische Kurzfassung; keine Vollübersetzung des englischen Fachmanuskripts.**

## Exakter Satz

S(k^n,1^m) bezeichnet den Baum mit ausgezeichnetem Zentrum, n Armen mit je k Kanten und m zusätzlichen Blättern am Zentrum. Tiefe ist der tatsächliche Graphabstand vom Zentrum. Ein graceful Labeling belegt die Knoten bijektiv mit0,…,N und die absoluten Kantendifferenzen bijektiv mit1,…,N, wobei N=nk+m.

Für jedes ganze k≥19 sei p=⌊(k−3)/2⌋. Definiere D8(k)=11 für19≤k≤34,27 für35≤k≤52 und25+16⌊(k−35)/18⌋ für53≤k≤124. Für k≥125 schreibe p=61+11a+r mit a≥0,0≤r≤10 und setze

```
F8(p)=107+20a+2r;
D8(k)=F8(p).
```

Für alle ganzen n≥2,m≥0,jeden ausgewählten langen Arm und jede ganze Tiefe2≤d≤D8(k) existiert ein graceful Labeling mit Null an dem verlangten Knoten. Verschiedene Wünsche dürfen verschiedene Labelings erfordern. Beide Paritäten, beliebige Blattzahlen und n=2,m=0 sind enthalten. Es gelten D8≥D7,D8<k und0≤10k−11D8(k)≤261, also D8(k)/k→10/11 entlang aller ganzen Armlängen. Die bisherigen K7-Schwellen bleiben hinreichend; eine neue exakte D8-Inverse wird hier nicht behauptet.

## Konstruktion und die Viererlücke

Verwendet werden die bereits akzeptierten kompatiblen Kerne der Größen16 und17. Ihre reflektierten Extrempaare beginnen jeweils in Tiefe26. Die positiven q9/q10/q11-Bausteine mit Präfixlänge2 bewahren die vollständigen Seiten-, Summen-, Endpunkt- und Fensterbedingungen. Nach der klassischen Umkehr-Komplement-Transformation liefern sie Tiefenzuwächse16,18,20. Alle Einfügungen erfolgen vor der einmaligen Reflexion.

Für die Basisgrößen62,64,66,68,70 liefern fünf Rezepte die fehlenden Paare108/109,112/113,116/117,120/121,124/125. Bei Größe71,Rest r=10, liegt die alte Grenze123 und die neue127: Ein Rezept aus Größe17 mit einem q10- und vier q11-Schritten liefert124/125; ein Rezept aus Größe16 mit fünf q11-Schritten liefert126/127. Nur das obere Paar würde eine Lücke lassen. Beide sind nötig.

Jede Zielgröße ist p=p0+11t mit61≤p0≤71. Zusätzliche t q11-Einfügungen vor der Reflexion erhöhen Größe und Tiefen um11t beziehungsweise20t. Damit füllen die übersetzten sieben Rezepte bei jeder Größe sämtliche Tiefen zwischen F7+1 und F8. Der akzeptierte D7-Satz liefert den unteren Bereich. Der D8-Zusatz benötigt keinen C6-Anhang; solche Anhänge gehören weiterhin zur getrennten D7-Beweisführung.

Die allgemeinen ungeraden und geraden Hüllen haben Alpha-Index und Mittelpunktlabel k−1 beziehungsweise k. Nach der Verklebung werden alle residualen Labels um A und die hohen Pfadlabels um die residuale Kantenzahl Q erhöht. Die Label- und Kantendifferenzintervalle partitionieren den gesamten tatsächlichen Spider. Null an einer H0-Position entsteht durch Komplementierung des vollständigen Graphen. Beide Richtungen des benachbarten Maximums sind erlaubt. Die Armauswahl ist beliebig; leere residuale Fälle sind eingeschlossen.

Substitution ergibt im neuen Zweig10k−11D8=73−2r+10ε,ε=0 oder1, mit Wertebereich53,…,83. Der alte Zweig behält den Maximalwert261 bei k124. Damit folgen legale Tiefen und der unveränderte Grenzanteil10/11. Die erste Verbesserung gegenüber D7 ist k127/128 von107 auf109; k145/146 verbessert123 auf127. Die Verbesserungen wiederholen sich nach22 zusätzlichen Kanten pro Arm.

## Nachweisstand und Grenzen

Der [separate mathematische Audit](research-audits/graceful-q10-gap-fill-independent-2026-10-09-a/report.md) bestätigt den exakten D8-Satz projektintern. Die genauen Quellen und Prüfsummen sind im README gebunden. Für den exakten D8-Satz liegen jetzt der vollständige formale Autorbeweis und ein getrennter Neuaufbau aus kopierten Quellen vor. Endliche Graphprüfungen stützen die universellen Identitäten und die unbeschränkte Rezeptübersetzung; sie ersetzen den Beweis nicht.

Keine Optimalität, vollständige Zero-Rotatability, gleichzeitigen Nullen, Tiefe eins, ungleichen Arme oder allgemeine Near-Tip-Abdeckung werden behauptet. Die historische Priorität ist ungeklärt; externe Begutachtung oder Peer Review ist nicht dokumentiert. Reflexion und Alpha-Verklebung sind klassische Operationen, deren ältere Zuschreibungen über zugängliche spätere Primärquellen vermittelt werden.

Jordi Gartner besitzt diese Arbeit und veröffentlicht sie über Beedbyte. KI-Werkzeuge unterstützten die dokumentierte Rezept- und Lückenrekonstruktion, symbolische Beweise und exakte projektinterne Prüfungen. Eine menschliche Sprachprüfung ist nicht dokumentiert. Vollständige Quellen und ältere Zertifikate stehen im englischen Manuskript und README.


Für die Vorgängersätze D6 und D7 liegen vollständige formale Autorbeweise und getrennte Neuaufbauten aus kopierten Quellen vor. D8 ist durch das neu gebundene separate Formalpaket abgedeckt. Die formalen Grenzwertaussagen verwenden ganzzahlige Präzisionskriterien, keine Lean-Real/Tendsto-Sätze.

Der neue [D8-Nachweis](research-audits/graceful-q10-gap-fill-lean-replay-2026-10-09-a/audit-report.md) umfasst den tatsächlichen indizierten Spider mit sämtlichen Parametern des Satzes, den universellen q10-Schritt, alle sieben Rezepte, die Viererlücke, unbeschränkte Übersetzung, Monotonie und Defizit261. Seine formale Grenzwertaussage ist ein ganzzahliges Präzisionskriterium. Ein Lean-Satz über Real/Tendsto, eine exakte K8-Inverse, Minimalität und maximale Abdeckung der Rezeptfamilie sind nicht enthalten. Die Prüfung ist relativ zum dokumentierten Lean-Kernel, Compiler, Std und den drei Standardaxiomen; sie ist keine externe Begutachtung. Die genaue Quellenbindung steht im README.