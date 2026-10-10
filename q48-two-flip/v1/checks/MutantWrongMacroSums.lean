import Q48Family
open GracefulBoundary
open GracefulBoundary.Q48Flip
set_option maxHeartbeats 0
set_option maxRecDepth 16384
example : inserted.Perm (List.range' 1 96) := by decide
