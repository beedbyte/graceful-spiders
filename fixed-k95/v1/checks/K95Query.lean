import K95Full
#print GracefulBoundary.K95Full.all_vertices
#print GracefulBoundary.K95Full.unique_zero
#check GracefulBoundary.K95Full.arm_depth_zero
#print axioms GracefulBoundary.K95Full.interior
#print axioms GracefulBoundary.K95Full.arm_depth_zero
#print axioms GracefulBoundary.K95Full.all_vertices
#print axioms GracefulBoundary.K95Full.unique_zero
#print axioms GracefulBoundary.K95Boundary.center_zero
#print axioms GracefulBoundary.K95Boundary.leaf_zero
#print axioms GracefulBoundary.K95Tip.tips_prescribed_zero
#print axioms GracefulBoundary.FiniteAlpha.prescribed_zero
open GracefulBoundary
example : ∃ f : SpiderVertex 2 0 95 → Nat, Graceful (spiderGraph 2 0 95) (95*2+0) f ∧ f SpiderVertex.center=0 := by
  exact K95Full.all_vertices 2 0 (by decide) SpiderVertex.center
example : ∃ f : SpiderVertex 2 0 95 → Nat, Graceful (spiderGraph 2 0 95) (95*2+0) f ∧ f (.arm (⟨0,by decide⟩ : Fin 2) (⟨0,by decide⟩ : Fin 95))=0 := by
  exact K95Full.all_vertices 2 0 (by decide) (.arm ⟨0,by decide⟩ ⟨0,by decide⟩)
example : ∃ f : SpiderVertex 2 0 95 → Nat, Graceful (spiderGraph 2 0 95) (95*2+0) f ∧ f (.arm (⟨1,by decide⟩ : Fin 2) (⟨73,by decide⟩ : Fin 95))=0 := by
  exact K95Full.all_vertices 2 0 (by decide) (.arm ⟨1,by decide⟩ ⟨73,by decide⟩)
example : ∃ f : SpiderVertex 2 0 95 → Nat, Graceful (spiderGraph 2 0 95) (95*2+0) f ∧ f (.arm (⟨0,by decide⟩ : Fin 2) (⟨86,by decide⟩ : Fin 95))=0 := by
  exact K95Full.all_vertices 2 0 (by decide) (.arm ⟨0,by decide⟩ ⟨86,by decide⟩)
example : ∃ f : SpiderVertex 2 0 95 → Nat, Graceful (spiderGraph 2 0 95) (95*2+0) f ∧ f (.arm (⟨1,by decide⟩ : Fin 2) (⟨91,by decide⟩ : Fin 95))=0 := by
  exact K95Full.all_vertices 2 0 (by decide) (.arm ⟨1,by decide⟩ ⟨91,by decide⟩)
example : ∃ f : SpiderVertex 2 0 95 → Nat, Graceful (spiderGraph 2 0 95) (95*2+0) f ∧ f (.arm (⟨0,by decide⟩ : Fin 2) (⟨93,by decide⟩ : Fin 95))=0 := by
  exact K95Full.all_vertices 2 0 (by decide) (.arm ⟨0,by decide⟩ ⟨93,by decide⟩)
example : ∃ f : SpiderVertex 2 0 95 → Nat, Graceful (spiderGraph 2 0 95) (95*2+0) f ∧ f (.arm (⟨1,by decide⟩ : Fin 2) (⟨94,by decide⟩ : Fin 95))=0 := by
  exact K95Full.all_vertices 2 0 (by decide) (.arm ⟨1,by decide⟩ ⟨94,by decide⟩)
example : ∃ f : SpiderVertex 2 1 95 → Nat, Graceful (spiderGraph 2 1 95) (95*2+1) f ∧ f (.leaf (⟨0,by decide⟩ : Fin 1))=0 := by
  exact K95Full.all_vertices 2 1 (by decide) (.leaf ⟨0,by decide⟩)
example : ∃ f : SpiderVertex 2 1 95 → Nat, Graceful (spiderGraph 2 1 95) (95*2+1) f ∧ f (.arm (⟨1,by decide⟩ : Fin 2) (⟨94,by decide⟩ : Fin 95))=0 := by
  exact K95Full.all_vertices 2 1 (by decide) (.arm ⟨1,by decide⟩ ⟨94,by decide⟩)
example : ∃ f : SpiderVertex 3 2 95 → Nat, Graceful (spiderGraph 3 2 95) (95*3+2) f ∧ f (.leaf (⟨1,by decide⟩ : Fin 2))=0 := by
  exact K95Full.all_vertices 3 2 (by decide) (.leaf ⟨1,by decide⟩)
example : ∃ f : SpiderVertex 3 2 95 → Nat, Graceful (spiderGraph 3 2 95) (95*3+2) f ∧ f (.arm (⟨2,by decide⟩ : Fin 3) (⟨91,by decide⟩ : Fin 95))=0 := by
  exact K95Full.all_vertices 3 2 (by decide) (.arm ⟨2,by decide⟩ ⟨91,by decide⟩)
example : ∃ f : SpiderVertex 2 0 95 → Nat, Graceful (spiderGraph 2 0 95) (95*2+0) f ∧ (∀ w, f w=0 ↔ w=(.arm (⟨1,by decide⟩ : Fin 2) (⟨94,by decide⟩ : Fin 95))) := by
  exact K95Full.unique_zero 2 0 (by decide) (.arm ⟨1,by decide⟩ ⟨94,by decide⟩)
example : ∃ f : SpiderVertex 2 1 95 → Nat, Graceful (spiderGraph 2 1 95) (95*2+1) f ∧ (∀ w, f w=0 ↔ w=(.leaf (⟨0,by decide⟩ : Fin 1))) := by
  exact K95Full.unique_zero 2 1 (by decide) (.leaf ⟨0,by decide⟩)
