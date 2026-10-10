import Q24Rooted
import RootedTriangle

open GracefulBoundary
open GracefulBoundary.Rooted71
open GracefulBoundary.Q24Rooted

-- This root has triangleLabel 1 = 1, not zero.
example := terminal_four triangle (⟨1, by decide⟩ : Fin 3)
  triangleLabel 3 1 (by decide) triangle_conventional (by decide)
