# Null-Rotierbarkeit von Spinnen mit Armen der Länge 25

> **Entwurf: deutsche Übersetzung; sprachlich nicht geprüft.**

Jordi Gartner veröffentlicht diese Arbeit über Beedbyte.

Sei S(25^n,1^m) die Spinne mit n benannten Armen aus jeweils 25 Kanten und m ursprünglichen Einheitsblättern am Zentrum. Für jedes n ≥ 2 und m ≥ 0 kann jeder tatsächlich vorhandene Knoten – das Zentrum, jede Tiefe von 1 bis 25 auf jedem benannten Arm und jedes vorhandene ursprüngliche Zentrumsblatt – in einer graziösen Beschriftung den Wert 0 erhalten. Die Beschriftung darf vom ausgewählten Knoten abhängen.

Die Konstruktion verbindet explizite graziöse Alpha-Beschriftungen von Pfaden mit 51 Knoten mit der klassischen Alpha-Amalgamation. Eine Restbeschriftung ergänzt die übrigen Arme und Blätter; gesonderte Konstruktionen behandeln das Zentrum, die ursprünglichen Blätter und die Armenden.

Frühere Arbeiten decken die vollständigen Pfadfälle n = 2, m = 0 und n = 2, m = 1 ab; Satz 14 von Luiz, Campos und Richter behandelt einen Pfad mit einem Zentrumsblatt. Shan und Zhong geben die klassische Alpha-Amalgamation wieder, die bei der Übertragung verwendet wird. Der vollständige feste-k25-Satz wird durch projektinterne mathematische Prüfungen und ein separates Lean-Replay des kopierten Quelltexts gestützt. Der begrenzte Vergleich klärt nicht, ob frühere Konstruktionen den gesamten Satz bereits umfassen; die historische Priorität bleibt daher ungeklärt.

## Methoden

KI-Werkzeuge unterstützten die Entwicklung der Konstruktion, die Formalisierung und Prüfung des Beweises sowie den Vergleich früherer Quellen; Lean 4.34.0 verifiziert den eingefrorenen Satz.
