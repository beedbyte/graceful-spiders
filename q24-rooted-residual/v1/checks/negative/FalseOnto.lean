import Q24Rooted
import RootedTriangle

open GracefulBoundary
open GracefulBoundary.Rooted71

-- Conventional graceful permits the omitted vertex label 2 in this cycle.
example : Graceful triangle 3 triangleLabel := by
  exact triangle_conventional
