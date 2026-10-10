import Init

namespace GracefulUniversalSeam

/-- The arithmetic input needed from the accepted D8 prefix is `R ≤ D`.
    The remaining three branches are: prefix, known deficits through 22,
    and a source radius from the proposed odd-q family. -/
def Covered (R D d : Nat) : Prop :=
  d ≤ D ∨ 2 * R - d ≤ 22 ∨
    ∃ q : Nat, 21 ≤ q ∧ q % 2 = 1 ∧
      (2 * R - d = q + 2 ∨ 2 * R - d = q + 3) ∧
      5 ≤ R - q + 2

theorem arithmetic_seam (R D d : Nat)
    (hD : R ≤ D) (hd0 : 2 ≤ d) (hd1 : d < 2 * R) :
    Covered R D d := by
  have hdpos : 2 ≤ d := hd0
  unfold Covered
  by_cases hp : d ≤ D
  · exact Or.inl hp
  right
  by_cases hl : 2 * R - d ≤ 22
  · exact Or.inl hl
  right
  by_cases he : (2 * R - d) % 2 = 0
  · refine ⟨(2 * R - d) - 3, ?_, ?_, ?_, ?_⟩
    all_goals omega
  · refine ⟨(2 * R - d) - 2, ?_, ?_, ?_, ?_⟩
    all_goals omega

/-- The same seam stated at the actual even arm length `k`.
    This is a numerical covering theorem, not a graph-labeling theorem. -/
theorem even_length_arithmetic_seam (k D d : Nat)
    (_hk : 36 ≤ k) (heven : k % 2 = 0) (hD : k / 2 ≤ D)
    (hd0 : 2 ≤ d) (hd1 : d < k) :
    Covered (k / 2) D d := by
  have hlen : k = 2 * (k / 2) := by omega
  exact arithmetic_seam (k / 2) D d hD hd0 (by omega)

/-- The first radius-family case is genuinely needed: c = 23, q = 21. -/
example : ∃ q : Nat, 21 ≤ q ∧ q % 2 = 1 ∧
    (2 * 25 - 27 = q + 2 ∨ 2 * 25 - 27 = q + 3) ∧
    5 ≤ 25 - q + 2 := by
  refine ⟨21, ?_⟩
  decide

/-- At the lower length boundary the last 22-deficit band suffices. -/
example : Covered 18 18 19 := arithmetic_seam 18 18 19 (by omega) (by omega) (by omega)

end GracefulUniversalSeam

#print axioms GracefulUniversalSeam.arithmetic_seam
#print axioms GracefulUniversalSeam.even_length_arithmetic_seam
