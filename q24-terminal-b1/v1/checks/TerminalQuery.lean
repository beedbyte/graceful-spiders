import Q24Terminal
#check GracefulBoundary.Q24Terminal.generic_source
#check GracefulBoundary.Q24Terminal.terminal_actual
#check GracefulBoundary.Q24Terminal.flip_certificate
#print axioms GracefulBoundary.Q24Terminal.fresh_high
#print axioms GracefulBoundary.Q24Terminal.fresh_low
#print axioms GracefulBoundary.Q24Terminal.fresh_sums
#print axioms GracefulBoundary.Q24Terminal.surgery_high
#print axioms GracefulBoundary.Q24Terminal.surgery_low
#print axioms GracefulBoundary.Q24Terminal.extend_sides
#print axioms GracefulBoundary.Q24Terminal.surgery_sums
#print axioms GracefulBoundary.Q24Terminal.enlarged_sums
#print axioms GracefulBoundary.Q24Terminal.extend_sums
#print axioms GracefulBoundary.Q24Terminal.extend_length
#print axioms GracefulBoundary.Q24Terminal.surgery_patch_index
#print axioms GracefulBoundary.Q24Terminal.extend_zeros
#print axioms GracefulBoundary.Q24Terminal.surgery_right_index
#print axioms GracefulBoundary.Q24Terminal.extend_midpoint
#print axioms GracefulBoundary.Q24Terminal.generic_source
#print axioms GracefulBoundary.Q24Terminal.flip_certificate
#print axioms GracefulBoundary.Q24Terminal.flip_actual
#print axioms GracefulBoundary.Q24Terminal.terminal_actual
open GracefulBoundary
example : P20Q24.DepthZero 2 0 47 42 (⟨0,by decide⟩ : Fin 2) := by
  exact (Q24Terminal.terminal_actual 1 2 0 (by decide) (by decide) ⟨0,by decide⟩).1
example : P20Q24.DepthZero 2 0 47 43 (⟨1,by decide⟩ : Fin 2) := by
  exact (Q24Terminal.terminal_actual 1 2 0 (by decide) (by decide) ⟨1,by decide⟩).2
example : P20Q24.DepthZero 2 1 47 42 (⟨1,by decide⟩ : Fin 2) := by
  exact (Q24Terminal.terminal_actual 1 2 1 (by decide) (by decide) ⟨1,by decide⟩).1
example : P20Q24.DepthZero 2 1 47 43 (⟨0,by decide⟩ : Fin 2) := by
  exact (Q24Terminal.terminal_actual 1 2 1 (by decide) (by decide) ⟨0,by decide⟩).2
example : P20Q24.DepthZero 3 2 143 130 (⟨2,by decide⟩ : Fin 3) := by
  exact (Q24Terminal.terminal_actual 5 3 2 (by decide) (by decide) ⟨2,by decide⟩).1
example : P20Q24.DepthZero 3 2 143 131 (⟨2,by decide⟩ : Fin 3) := by
  exact (Q24Terminal.terminal_actual 5 3 2 (by decide) (by decide) ⟨2,by decide⟩).2
