import Q24Rooted
import RootedTriangle

open GracefulBoundary
open GracefulBoundary.Rooted71
open GracefulBoundary.Q24Rooted

-- The first terminal_four projection gives index 5, not the midpoint 47.
example : ZeroAt triangle (⟨0, by decide⟩ : Fin 3) 3 22
    (⟨47, by decide⟩ : Fin 95) := by
  have h := terminal_four triangle (⟨0, by decide⟩ : Fin 3)
    triangleLabel 3 1 (by decide) triangle_conventional (by decide)
  exact h.1
