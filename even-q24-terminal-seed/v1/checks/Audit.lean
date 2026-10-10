import K30Seed
import Lean
open GracefulBoundary GracefulBoundary.Rooted71 GracefulBoundary.EvenSeedFamily

def triangle : IndexedGraph (Fin 3) (Fin 3) where
  source e := e
  target e := ⟨(e.val+1)%3,by omega⟩

def triangleLabel (v : Fin 3) : Nat := if v.val=0 then 0 else if v.val=1 then 1 else 3

theorem triangle_graceful : ConventionalGraceful triangle 3 triangleLabel := by
  constructor
  · constructor <;> decide
  · constructor
    · decide
    · decide
    · intro x hx htop
      have hc : x=1 ∨ x=2 ∨ x=3 := by omega
      rcases hc with rfl | rfl | rfl
      · exact ⟨⟨0,by decide⟩,by decide⟩
      · exact ⟨⟨1,by decide⟩,by decide⟩
      · exact ⟨⟨2,by decide⟩,by decide⟩

def disconnected : IndexedGraph (Fin 4) (Fin 3) where
  source e := ⟨e.val,by omega⟩
  target e := ⟨(e.val+1)%3,by omega⟩

def disconnectedLabel (v : Fin 4) : Nat :=
  if v.val=0 then 0 else if v.val=1 then 1 else if v.val=2 then 3 else 2

theorem disconnected_graceful : ConventionalGraceful disconnected 3 disconnectedLabel := by
  constructor
  · constructor <;> decide
  · constructor
    · decide
    · decide
    · intro x hx htop
      have hc : x=1 ∨ x=2 ∨ x=3 := by omega
      rcases hc with rfl | rfl | rfl
      · exact ⟨⟨0,by decide⟩,by decide⟩
      · exact ⟨⟨1,by decide⟩,by decide⟩
      · exact ⟨⟨2,by decide⟩,by decide⟩

example : ¬∃ v, triangleLabel v=2 := by decide
example : EvenRootedPrefix.ZeroAt triangle ⟨0,by decide⟩ 3 30 ⟨4,by decide⟩ ∧
    EvenRootedPrefix.ZeroAt triangle ⟨0,by decide⟩ 3 30 ⟨56,by decide⟩ :=
  k30_window triangle ⟨0,by decide⟩ triangleLabel 3 0 26 triangle_graceful
    (by decide) (by decide) (by decide)
example : EvenRootedPrefix.ZeroAt disconnected ⟨0,by decide⟩ 3 126 ⟨11,by decide⟩ ∧
    EvenRootedPrefix.ZeroAt disconnected ⟨0,by decide⟩ 3 126 ⟨241,by decide⟩ :=
  k30_joined_prefix disconnected ⟨0,by decide⟩ disconnectedLabel 3 4 115
    disconnected_graceful (by decide) (by decide) ⟨by decide,by decide⟩

#check @EvenSeedFamily.all_states
#check @EvenSeedFamily.rooted_window
#check @EvenSeedFamily.k30_window
#check @EvenSeedFamily.k28_window
#check @EvenSeedFamily.k30_joined_prefix
#print axioms EvenSeedFamily.all_states
#print axioms EvenSeedFamily.rooted_window
#print axioms EvenSeedFamily.seed30_valid
#print axioms EvenSeedFamily.seed28_valid
#print axioms EvenSeedFamily.k30_window
#print axioms EvenSeedFamily.k28_window
#print axioms EvenSeedFamily.k30_D8_identity
#print axioms EvenSeedFamily.k30_exact_seam
#print axioms EvenSeedFamily.k30_joined_prefix

namespace Checks
theorem root_zero_retained : triangleLabel ⟨0,by decide⟩=0 := by decide
end Checks
