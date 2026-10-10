import ThreeArmLeaves
namespace GracefulBoundary.FixedEven

abbrev gains (k B x : Nat) : Prop := x%k≠0 ∨ B≤x
def gapWeight (k B x : Nat) := if gains k B x then x+k else x
def gapWeights {E : Type} (w : E → Nat) (k B : Nat) : Sum E (Fin k) → Nat
  | .inl e => gapWeight k B (w e)
  | .inr d => if d.val=0 then B else d.val

theorem multiple_separation (k a b : Nat) (ha : a%k=0) (hb : b%k=0) (hlt : a<b) : a+k≤b := by
  have dvd := Nat.dvd_sub (Nat.dvd_of_mod_eq_zero hb) (Nat.dvd_of_mod_eq_zero ha)
  have lower := Nat.le_of_dvd (by omega : 0<b-a) dvd
  omega

theorem gapWeight_mod (k B x : Nat) : gapWeight k B x%k=x%k := by
  dsimp only [gapWeight]; split
  · exact Nat.add_mod_right x k
  · rfl

theorem gapWeight_injective (k B x y : Nat) (hk : 1≤k) (he : gapWeight k B x=gapWeight k B y) : x=y := by
  have modEq : x%k=y%k := by rw [←gapWeight_mod k B x,←gapWeight_mod k B y,he]
  dsimp only [gapWeight,gains] at he
  repeat (any_goals (first | omega | split at he))

/-- Exact abstract edge-weight partition for a single-gap arm insertion. -/
theorem gap_weight_bijection {E : Type} (w : E → Nat) (q k B : Nat)
    (hw : BandBijection w 1 q) (hk : 1≤k) (hB : k≤B ∧ B≤q) (hm : B%k=0) :
    BandBijection (gapWeights w k B) 1 (q+k) := by
  constructor
  · intro e; cases e with
    | inl e => have := hw.bounds e; dsimp only [gapWeights,gapWeight]; split <;> omega
    | inr d => dsimp only [gapWeights]; split <;> have := d.isLt <;> omega
  · intro e f he; cases e with
    | inl e => cases f with
      | inl f => exact congrArg Sum.inl (hw.injective _ _ (gapWeight_injective k B _ _ hk he))
      | inr d =>
        have hemod := gapWeight_mod k B (w e)
        have bound := hw.bounds e
        dsimp only [gapWeights] at he
        by_cases hd : d.val=0
        · rw [ite_eq_left hd] at he
          have oldMod : w e%k=0 := by rw [←hemod,he,hm]
          dsimp only [gapWeight,gains] at he
          split at he <;> omega
        · rw [ite_eq_right hd] at he
          dsimp only [gapWeight,gains] at he
          split at he
          · have := d.isLt; omega
          · have oldMod : w e%k=0 := by omega
            have lt : w e<k := by have := d.isLt; omega
            have zero := Nat.mod_eq_of_lt lt
            omega
    | inr d => cases f with
      | inl f =>
        have hemod := gapWeight_mod k B (w f)
        have bound := hw.bounds f
        dsimp only [gapWeights] at he
        by_cases hd : d.val=0
        · rw [ite_eq_left hd] at he
          have oldMod : w f%k=0 := by rw [←hemod,←he,hm]
          dsimp only [gapWeight,gains] at he
          split at he <;> omega
        · rw [ite_eq_right hd] at he
          dsimp only [gapWeight,gains] at he
          split at he
          · have := d.isLt; omega
          · have oldMod : w f%k=0 := by omega
            have lt : w f<k := by have := d.isLt; omega
            have zero := Nat.mod_eq_of_lt lt
            omega
      | inr f =>
        dsimp only [gapWeights] at he
        congr 1; apply Fin.ext
        have := d.isLt; have := f.isLt
        repeat (any_goals (first | omega | split at he))
  · intro y hy hq
    by_cases small : y<k
    · exact ⟨.inr ⟨y,small⟩,by dsimp only [gapWeights]; rw [ite_eq_right (by omega)]⟩
    · by_cases bridge : y=B
      · exact ⟨.inr ⟨0,by omega⟩,by simp only [gapWeights,ite_true,bridge]⟩
      · by_cases fixed : y%k=0 ∧ y<B
        · obtain ⟨e,he⟩ := hw.onto y hy (by omega)
          refine ⟨.inl e,?_⟩
          dsimp only [gapWeights,gapWeight]
          rw [he,ite_eq_right (by dsimp only [gains]; omega)]
        · have xpositive : 1≤y-k := by
            by_cases eq : y=k
            · have ymod : y%k=0 := by rw [eq]; exact Nat.mod_self k
              omega
            · omega
          obtain ⟨e,he⟩ := hw.onto (y-k) xpositive (by omega)
          have xmod : (y-k)%k=y%k := (Nat.mod_eq_sub_mod (by omega)).symm
          have cross : gains k B (y-k) := by
            dsimp only [gains]
            by_cases nz : y%k≠0
            · exact Or.inl (by rw [xmod]; exact nz)
            · have ymod : y%k=0 := by omega
              have sep := multiple_separation k B y hm ymod (by omega)
              exact Or.inr (by omega)
          refine ⟨.inl e,?_⟩
          dsimp only [gapWeights,gapWeight]
          rw [he,ite_eq_left cross]
          omega

end GracefulBoundary.FixedEven
