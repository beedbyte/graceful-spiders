import K95Full
open GracefulBoundary
example : ∃ f : SpiderVertex 2 0 94 → Nat, Graceful (spiderGraph 2 0 94) 188 f ∧ f SpiderVertex.center=0 := by
  exact K95Full.all_vertices 2 0 (by decide) SpiderVertex.center
