import Positive
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open GracefulBoundary GracefulBoundary.Rooted71 Audit
example : (TerminalSeed12.labels 1)[119]?=some 119 := by decide
