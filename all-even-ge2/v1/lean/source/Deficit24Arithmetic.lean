import Deficit24Seeds
namespace GracefulBoundary.Deficit24

def lengths : List Nat := [46,48,50,52,54,56,58,60,62,64,66,72,74,76,78,80,82,90,92,94,96,98,108,110,112,114,126,128,130,132,134,136,138,140,142,144,146,148,150,152,154,156,158,160,162,164,166,168,170,172,174,176,178,180,182,184,186,188,190,192,194,196,198,200,202,204,206,208,210,212]

theorem length_count : lengths.length=70 := by decide
theorem finite_arithmetic_gate : ∀k,k∈lengths → 46≤k ∧ k%2=0 ∧ k-25≤GapFill.depthPrefix k := by decide

theorem high_branch_deficit (k : Nat) (hk : 126≤k) (heven : k%2=0) :
    k-GapFill.depthPrefix k=19+2*((((k-3)/2)-61)/11) := by
  unfold GapFill.depthPrefix GapFill.F
  simp only [show ¬k≤124 by omega,ite_false]
  omega

theorem no_seam_beyond212 (k : Nat) (hk : 214≤k) (heven : k%2=0) :
    GapFill.depthPrefix k<k-25 := by
  have diff := high_branch_deficit k (by omega) heven
  have inside := GapFill.prefix_inside k (by omega)
  omega

set_option maxRecDepth 4096 in
theorem finite_seam_table : ∀k,k≤212 →
    (46≤k ∧ k%2=0 ∧ k-25≤GapFill.depthPrefix k ↔ k∈lengths) := by decide

theorem exact_composition_criterion (k : Nat) :
    (46≤k ∧ k%2=0 ∧ k-25≤GapFill.depthPrefix k) ↔ k∈lengths := by
  by_cases bound : k≤212
  · exact finite_seam_table k bound
  · constructor
    · intro ⟨hk,heven,seam⟩
      have impossible := no_seam_beyond212 k (by omega) heven
      omega
    · intro member
      have small : ∀k,k∈lengths → k≤212 := by decide
      exact False.elim (bound (small k member))

theorem k214_fails_criterion : GapFill.depthPrefix 214<214-25 := by decide
theorem k44_not_listed : 44∉lengths := by decide

end GracefulBoundary.Deficit24
