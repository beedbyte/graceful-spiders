import RootedActual

namespace GracefulBoundary.Rooted71

/-- A three-edge cycle whose graceful vertex labels omit 2. -/
def triangle : IndexedGraph (Fin 3) (Fin 3) where
  source e := if e.val=1 then ⟨1,by decide⟩ else ⟨0,by decide⟩
  target e := if e.val=0 then ⟨1,by decide⟩ else ⟨2,by decide⟩

def triangleLabel (v : Fin 3) : Nat :=
  if v.val=0 then 0 else if v.val=1 then 1 else 3

theorem triangle_conventional : ConventionalGraceful triangle 3 triangleLabel := by
  constructor
  · constructor
    · decide
    · decide
  · constructor
    · decide
    · decide
    · intro x hx htop
      have hcases : x=1 ∨ x=2 ∨ x=3 := by omega
      rcases hcases with h|h|h
      · exact ⟨⟨0,by decide⟩,by simp [h,weight,triangle,triangleLabel,distance]⟩
      · exact ⟨⟨1,by decide⟩,by simp [h,weight,triangle,triangleLabel,distance]⟩
      · exact ⟨⟨2,by decide⟩,by simp [h,weight,triangle,triangleLabel,distance]⟩

theorem triangle_not_onto : ¬ Graceful triangle 3 triangleLabel := by
  intro h
  obtain ⟨v,hv⟩ := h.vertices.onto 2 (by decide) (by decide)
  have hnone : ∀ v : Fin 3, triangleLabel v≠2 := by decide
  exact hnone v hv

theorem triangle_new_arms (d : Nat) (hd : 1≤d ∧ d≤70) (right : Bool) :
    ∃ f : GraftVertices (Fin 143) (Fin 3) midpoint → Nat,
      ConventionalGraceful (graftGraph (pathGraph 142) triangle midpoint ⟨0,by decide⟩)
        145 f ∧ f (graftEmbed midpoint ⟨0,by decide⟩ (selectedPoint d hd right))=0 := by
  simpa using conventional_new_arm triangle ⟨0,by decide⟩ triangleLabel 3
    triangle_conventional rfl d hd right

end GracefulBoundary.Rooted71
