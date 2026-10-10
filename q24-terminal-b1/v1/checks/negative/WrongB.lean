import Q24Terminal
open GracefulBoundary
example : (edgeSums (25::[15,0]) ++ edgeSums (0::Q24Terminal.D++[26]) ++ edgeSums (36::Q24Terminal.A)).Perm (List.range' 1 50) := by decide
