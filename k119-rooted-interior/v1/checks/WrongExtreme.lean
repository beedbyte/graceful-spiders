import Positive
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open GracefulBoundary GracefulBoundary.Rooted71 Audit
example : (TerminalSeed34.labels 1)[4]?=some 0 := by decide
