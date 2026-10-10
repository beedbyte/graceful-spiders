import DischargedWrapper
import D8HalfLength
import K18Full
import K24Full
import K26Full
import K28Full
import K30Full
import K32Full
import K34Full

namespace GracefulBoundary.Integration

/-- The universal interior, boundary, source, graft, and numeric depth inputs
    have all been discharged in the imported packages. -/
theorem large_even_actual (R n m : Nat) (hR : 18 ≤ R) (hn : 2 ≤ n)
    (v : SpiderVertex n m (2*R)) :
    ∃ f : SpiderVertex n m (2*R) → Nat,
      Graceful (spiderGraph n m (2*R)) (n*(2*R)+m) f ∧ f v = 0 :=
  LowBand.full_actual_if_D8 R n m hR hn
    (D8HalfLength.even_radius_half_length R hR) v

/-- Fixed even arm lengths 18 through 34, with each exact theorem named. -/
theorem fixed_18_34_actual (k n m : Nat)
    (hk : k=18 ∨ k=20 ∨ k=22 ∨ k=24 ∨ k=26 ∨
      k=28 ∨ k=30 ∨ k=32 ∨ k=34) (hn : 2 ≤ n)
    (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f v = 0 := by
  rcases hk with h|h|h|h|h|h|h|h|h <;> subst k
  · exact K18.full_zero_rotatability n m hn v
  · exact FullFixed.fixed_full_zero_rotatability 20 n m (Or.inl rfl) hn v
  · exact FullFixed.fixed_full_zero_rotatability 22 n m (Or.inr rfl) hn v
  · exact FullFixed24.k24_full_zero_rotatability n m hn v
  · exact FullFixed26.k26_full_zero_rotatability n m hn v
  · exact FullFixed28.k28_full_zero_rotatability n m hn v
  · exact FullFixed30.k30_full_zero_rotatability n m hn v
  · exact FullFixed32.k32_full_zero_rotatability n m hn v
  · exact FullFixed34.k34_full_zero_rotatability n m hn v

/-- Complete even-length theorem for the exact range k≥18, n≥2. -/
theorem all_even_ge_18_actual (k n m : Nat) (hk : 18 ≤ k)
    (heven : k % 2 = 0) (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f v = 0 := by
  by_cases hsmall : k ≤ 34
  · apply fixed_18_34_actual k n m _ hn v
    omega
  · obtain ⟨R, hR, rfl⟩ : ∃ R, 18 ≤ R ∧ k = 2*R :=
      ⟨k/2, by omega, by omega⟩
    exact large_even_actual R n m hR hn v

/-- Gracefulness gives uniqueness of the requested zero in each labeling. -/
theorem all_even_ge_18_unique_zero (k n m : Nat) (hk : 18 ≤ k)
    (heven : k % 2 = 0) (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧
      f v = 0 ∧ ∀ w, w ≠ v → 0 < f w := by
  obtain ⟨f, hf, hz⟩ := all_even_ge_18_actual k n m hk heven hn v
  refine ⟨f, hf, hz, ?_⟩
  intro w hw
  have hnonzero : f w ≠ 0 := by
    intro hzero
    exact hw (hf.vertices.injective w v (hzero.trans hz.symm))
  omega

end GracefulBoundary.Integration

#print axioms GracefulBoundary.Integration.large_even_actual
#print axioms GracefulBoundary.Integration.fixed_18_34_actual
#print axioms GracefulBoundary.Integration.all_even_ge_18_actual
#print axioms GracefulBoundary.Integration.all_even_ge_18_unique_zero
