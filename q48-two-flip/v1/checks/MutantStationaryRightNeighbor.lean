import Q48Family
open GracefulBoundary
open GracefulBoundary.Q48Flip
set_option maxHeartbeats 0
set_option maxRecDepth 16384
example : (terminalWord 0)[7]?=some 2 := by decide
