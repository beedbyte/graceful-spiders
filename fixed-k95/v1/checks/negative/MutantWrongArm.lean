import K95Full
open GracefulBoundary
example : ∃ f : SpiderVertex 2 0 95 → Nat, Graceful (spiderGraph 2 0 95) 190 f ∧ f (.arm (⟨2,by decide⟩ : Fin 2) (⟨94,by decide⟩ : Fin 95))=0 := by
  exact K95Full.all_vertices 2 0 (by decide) (.arm ⟨2,by decide⟩ ⟨94,by decide⟩)
