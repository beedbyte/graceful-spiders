# Ein wachsendes Nulltiefen-Intervall für Spinnen mit gleich langen Armen

**Beedbyte.** Jordi Gartner veröffentlicht diese Arbeit über Beedbyte.

*Übersetzungsentwurf; eine menschliche Sprachprüfung ist nicht dokumentiert.*

Für jede ganze Zahl t≥0 sei k=23+24t. Für jedes n≥2, m≥0, jeden benannten langen Arm a und jede Tiefe d mit 17+20t≤d≤20+22t kann der tatsächlich vorhandene Knoten in Tiefe d auf Arm a von S(k^n,1^m) in einer graziösen Beschriftung den Wert 0 erhalten. Für jedes Arm-Tiefen-Ziel darf eine eigene Beschriftung verwendet werden. Das Intervall umfasst 4+2t Tiefen: Bei k=47 reicht es von 37 bis 42, bei k=71 von 57 bis 64. Die Aussage gilt nur für diese Tiefen, nicht für alle Knoten bei diesen Armlängen.

Die Konstruktion beginnt mit zwei 47-knotigen Mittelpunkt-Alpha-Beschriftungen eines Pfades und erweitert sie mit den q24-B2- und B4-Anfügungen in beliebiger Reihenfolge. Ihre Nullpositionen ergeben zwei Tiefenbereiche, die sich berühren oder überschneiden und zusammen das ganze Intervall abdecken. Die Pfadbeschriftungen werden auf zwei ausgewählte Arme der tatsächlichen Spinne übertragen; eine Restkonstruktion ergänzt die graziöse Beschriftung auf allen übrigen Armen und ursprünglichen Zentrumsblättern. So gilt derselbe Tiefenbereich für alle n≥2 und m≥0.

Für t=0 liegt das Intervall im zuvor bewiesenen vollständigen Fall k=23. Für jedes t sind auch die Pfad-Unterfamilien n=2,m=0 und n=2,m=1 durch frühere Pfadergebnisse abgedeckt: durch Rosas Pfadergebnis in der Wiedergabe von Luiz, Campos und Richter sowie durch deren Satz 14 für einen Pfad mit einem Zentrumsblatt. Der Beweis nutzt die klassische Alpha-Amalgamation, wie sie Shan und Zhong wiedergeben, als früheres Konstruktionswerkzeug.

Methoden: KI-Werkzeuge unterstützten die Entwicklung der gemischten B2/B4-Konstruktion und des Lean-Beweises; Lean 4.34.0 prüft den eingefrorenen formalen Satz.

Prüfungen durch getrennte KI-Agenten sind projektinterne Prüfungen, keine externe wissenschaftliche Begutachtung.

## Quellen

- [Luiz, Campos und Richter, Bericht IC-17-12, Lemma 4 und Satz 14 (Pfadfälle).](https://ic.unicamp.br/~reltech/2017/17-12.pdf)
- [Shan und Zhong, Graziöse Beschriftung zweier Spinnenfamilien, Lemma 1 (klassische Alpha-Amalgamation).](https://arxiv.org/html/2605.14295v2)
- [Beedbyte, Forschungsnotiz fixed-k23/v1 (früherer vollständiger Fall k=23, Quellrevision b7546e3aac1a25e6a62c1a9eeb8794049ad093ed).](https://github.com/beedbyte/graceful-spiders/blob/b7546e3aac1a25e6a62c1a9eeb8794049ad093ed/fixed-k23/v1/note.en.md)
