import Q24Rooted
import RootedTriangle

open GracefulBoundary
open GracefulBoundary.Rooted71
open GracefulBoundary.Q24Rooted

#check GracefulBoundary.Q24Rooted.terminal_four
#check GracefulBoundary.Q24Rooted.ZeroAt
#print axioms GracefulBoundary.Q24Rooted.reverse_certificate
#print axioms GracefulBoundary.Q24Rooted.rooted_extreme
#print axioms GracefulBoundary.Q24Rooted.rooted_left
#print axioms GracefulBoundary.Q24Rooted.rooted_right
#print axioms GracefulBoundary.Q24Rooted.terminal_parameters
#print axioms GracefulBoundary.Q24Rooted.terminal_four_s
#print axioms GracefulBoundary.Q24Rooted.terminal_four
#print axioms GracefulBoundary.Rooted71.triangle_conventional
#print axioms GracefulBoundary.Rooted71.triangle_not_onto

theorem triangle_rooted_t1_left0 :
    ZeroAt triangle (⟨0, by decide⟩ : Fin 3) 3 22
      (⟨5, by decide⟩ : Fin 95) := by
  have h := terminal_four triangle (⟨0, by decide⟩ : Fin 3)
    triangleLabel 3 1 (by decide) triangle_conventional (by decide)
  exact h.1

theorem triangle_rooted_t1_all_four :
    ZeroAt triangle (⟨0, by decide⟩ : Fin 3) 3 22
      (⟨5, by decide⟩ : Fin 95) ∧
    ZeroAt triangle (⟨0, by decide⟩ : Fin 3) 3 22
      (⟨4, by decide⟩ : Fin 95) ∧
    ZeroAt triangle (⟨0, by decide⟩ : Fin 3) 3 22
      (⟨89, by decide⟩ : Fin 95) ∧
    ZeroAt triangle (⟨0, by decide⟩ : Fin 3) 3 22
      (⟨90, by decide⟩ : Fin 95) := by
  have h := terminal_four triangle (⟨0, by decide⟩ : Fin 3)
    triangleLabel 3 1 (by decide) triangle_conventional (by decide)
  exact h

theorem triangle_strict_onto_false : ¬ Graceful triangle 3 triangleLabel :=
  triangle_not_onto
