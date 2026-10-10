import EvenRootedPrefix
import Lean

open GracefulBoundary GracefulBoundary.Rooted71 GracefulBoundary.EvenRootedPrefix

namespace Replay
def triangle : IndexedGraph (Fin 3) (Fin 3) where
  source e := e
  target e := ⟨(e.val+1)%3, by omega⟩
def lab (v : Fin 3) : Nat := if v.val=0 then 0 else if v.val=1 then 1 else 3
theorem conventional : ConventionalGraceful triangle 3 lab := by
  constructor
  · constructor <;> decide
  · constructor
    · decide
    · decide
    · intro x hx htop
      have hc : x=1 ∨ x=2 ∨ x=3 := by omega
      rcases hc with rfl|rfl|rfl
      · exact ⟨⟨0,by decide⟩,by decide⟩
      · exact ⟨⟨1,by decide⟩,by decide⟩
      · exact ⟨⟨2,by decide⟩,by decide⟩
theorem not_onto : ¬ Graceful triangle 3 lab := by
  intro h
  obtain ⟨v,hv⟩ := h.vertices.onto 2 (by decide) (by decide)
  have impossible : ∀ v : Fin 3, lab v≠2 := by decide
  exact impossible v hv
end Replay
