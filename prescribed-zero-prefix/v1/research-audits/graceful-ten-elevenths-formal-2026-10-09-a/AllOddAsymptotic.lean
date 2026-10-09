import AllOddDepth

namespace GracefulBoundary.AllOdd

theorem prefix_error_bound (k : Nat) (hk : 19≤k) (hodd : k%2=1) :
    6*depthPrefix k≤5*k ∧ 5*k-6*depthPrefix k≤127 := by
  unfold depthPrefix upper
  omega

/-- A reciprocal-precision, cross-multiplied ratio-convergence criterion.
    No Real topology or division structure is imported by this definition. -/
def ReciprocalPrecisionLimit (f : Nat → Nat) (numerator denominator : Nat) : Prop :=
  ∀ precision : Nat, ∃ cutoff : Nat, ∀ k : Nat, cutoff≤k → k%2=1 →
    precision*distance (denominator*f k) (numerator*k)<k

theorem prefix_ratio_precision_limit : ReciprocalPrecisionLimit depthPrefix 5 6 := by
  intro precision
  refine ⟨128*precision+19,?_⟩
  intro k hk hodd
  have bounds := prefix_error_bound k (by omega) hodd
  have metric : distance (6*depthPrefix k) (5*k)=5*k-6*depthPrefix k := by
    unfold distance
    omega
  rw [metric]
  have multiplied := Nat.mul_le_mul_left precision bounds.2
  have target : precision*127<k := by
    rw [Nat.mul_comm precision 127]
    omega
  exact Nat.lt_of_le_of_lt multiplied target

end GracefulBoundary.AllOdd
