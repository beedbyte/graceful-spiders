import K95Full
open GracefulBoundary
example : ∃ f : SpiderVertex 2 1 95 → Nat, Graceful (spiderGraph 2 1 95) (95*2) f ∧ f SpiderVertex.center=0 := by
  exact K95Full.all_vertices 2 1 (by decide) SpiderVertex.center
