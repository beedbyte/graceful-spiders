import K95Full
open GracefulBoundary
example : ∃ f : SpiderVertex 1 0 95 → Nat, Graceful (spiderGraph 1 0 95) 95 f ∧ f SpiderVertex.center=0 := by
  exact K95Full.all_vertices 1 0 (by decide) SpiderVertex.center
