import GapDepth
namespace GracefulBoundary.D8HalfLength

theorem branch35_52 (k : Nat) (hk : 35≤k ∧ k≤52) : GapFill.depthPrefix k=27 := by
  unfold GapFill.depthPrefix Q11.depthPrefix ReverseComplement.depthPrefix
  simp only [show k≤124 by omega,show ¬k≤34 by omega,hk.2,ite_true,ite_false]

theorem branch53_124 (k : Nat) (hk : 53≤k ∧ k≤124) :
    GapFill.depthPrefix k=25+16*((k-35)/18) := by
  unfold GapFill.depthPrefix Q11.depthPrefix ReverseComplement.depthPrefix
  simp only [hk.2,show ¬k≤34 by omega,show ¬k≤52 by omega,ite_true,ite_false]

theorem branch125_up (k : Nat) (hk : 125≤k) :
    GapFill.depthPrefix k=107+20*((((k-3)/2)-61)/11)+2*((((k-3)/2)-61)%11) := by
  unfold GapFill.depthPrefix GapFill.F
  simp only [show ¬k≤124 by omega,ite_false]

/-- Stronger than the even-only target: exact current D8 dominates floor(k/2) for every k>=35. -/
theorem all_lengths_half_length (k : Nat) (hk : 35≤k) : k/2≤GapFill.depthPrefix k := by
  by_cases low : k≤52
  · rw [branch35_52 k ⟨hk,low⟩]; omega
  by_cases middle : k≤124
  · rw [branch53_124 k ⟨by omega,middle⟩]; omega
  · have bound := GapFill.tail_error_bound k (by omega)
    omega

/-- Requested exact all-even consequence, tied directly to the frozen D8 function. -/
theorem even_half_length (k : Nat) (hk : 36≤k) (_heven : k%2=0) :
    k/2≤GapFill.depthPrefix k := all_lengths_half_length k (by omega)

theorem even_radius_half_length (R : Nat) (hR : 18≤R) : R≤GapFill.depthPrefix (2*R) := by
  have bound := even_half_length (2*R) (by omega) (by omega)
  simpa only [Nat.mul_div_cancel_left _ (by decide : 0<2)] using bound

theorem k34_boundary_failure : GapFill.depthPrefix 34<34/2 := by decide
theorem exact_d8_at98 : GapFill.depthPrefix 98=73 := by decide
theorem old_compatible_at98 : Compatible.depthPrefix 98=71 := by decide
theorem d8_is_not_old_compatible : GapFill.depthPrefix 98≠Compatible.depthPrefix 98 := by decide

end GracefulBoundary.D8HalfLength
