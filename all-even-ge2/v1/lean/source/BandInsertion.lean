import ArmSymmetry

namespace GracefulBoundary.CenterLeaves

def insertLabel {V : Type} (f : V → Nat) (t m : Nat) : Sum V (Fin m) → Nat
  | .inl v => if t≤f v then f v+m else f v
  | .inr j => t+j.val

theorem band_insert {V : Type} (f : V → Nat) (lo q t m : Nat)
    (hf : BandBijection f lo q) (ht : lo≤t ∧ t≤q+1) :
    BandBijection (insertLabel f t m) lo (q+m) := by
  constructor
  · intro v; cases v with
    | inl v => have := hf.bounds v; dsimp only [insertLabel]; split <;> omega
    | inr j => dsimp only [insertLabel]; have := j.isLt; omega
  · intro v w he; cases v with
    | inl v => cases w with
      | inl w =>
        have hv := hf.bounds v; have hw := hf.bounds w
        have eq : f v=f w := by dsimp only [insertLabel] at he; repeat (any_goals (first | omega | split at he))
        exact congrArg Sum.inl (hf.injective _ _ eq)
      | inr j => dsimp only [insertLabel] at he; split at he <;> have := j.isLt <;> omega
    | inr i => cases w with
      | inl w => dsimp only [insertLabel] at he; split at he <;> have := i.isLt <;> omega
      | inr j => congr 1; apply Fin.ext; dsimp only [insertLabel] at he; omega
  · intro x hx hq
    by_cases low : x<t
    · obtain ⟨v,hv⟩ := hf.onto x hx (by omega)
      exact ⟨.inl v,by dsimp only [insertLabel]; rw [hv,ite_eq_right (by omega)]⟩
    · by_cases gap : x<t+m
      · exact ⟨.inr ⟨x-t,by omega⟩,by dsimp only [insertLabel]; omega⟩
      · obtain ⟨v,hv⟩ := hf.onto (x-m) (by omega) (by omega)
        refine ⟨.inl v,?_⟩
        dsimp only [insertLabel]
        rw [hv,ite_eq_left (by omega)]
        omega

end GracefulBoundary.CenterLeaves
