import CompatibleDepth

namespace GracefulBoundary.Compatible

theorem prefix_error_bound (k : Nat) (hk : 19≤k) :
    6*depthPrefix k≤5*k ∧ 5*k-6*depthPrefix k≤104 := by
  unfold depthPrefix upper
  split <;> omega

theorem prefix_ratio_precision_limit :
    ∀ precision : Nat, ∃ cutoff : Nat, ∀ k : Nat, cutoff≤k →
      precision*distance (6*depthPrefix k) (5*k)<k := by
  intro precision
  refine ⟨105*precision+19,?_⟩
  intro k hk
  have bound := prefix_error_bound k (by omega)
  have diff : distance (6*depthPrefix k) (5*k)≤104 := by
    unfold distance
    omega
  have product := Nat.mul_le_mul_left precision diff
  have eq : precision*104=104*precision := Nat.mul_comm _ _
  omega

end GracefulBoundary.Compatible
