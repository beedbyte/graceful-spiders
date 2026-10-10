import K16Existing
import AllEvenIntegration

namespace GracefulBoundary.Integration16

/-- Every actual named vertex of every even-length spider from k=16 onward
    can be zero in its own graceful labeling. -/
theorem all_even_ge_16_actual (k n m : Nat) (hk : 16 ≤ k)
    (heven : k % 2 = 0) (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f v = 0 := by
  by_cases h16 : k = 16
  · subst k
    exact K16Existing.full_actual n m hn v
  · exact Integration.all_even_ge_18_actual k n m (by omega) heven hn v

/-- Injectivity of graceful labels makes the chosen zero unique. -/
theorem all_even_ge_16_unique_zero (k n m : Nat) (hk : 16 ≤ k)
    (heven : k % 2 = 0) (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧
      f v = 0 ∧ ∀ w, w ≠ v → 0 < f w := by
  obtain ⟨f,hf,hz⟩ := all_even_ge_16_actual k n m hk heven hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have hnonzero : f w ≠ 0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.Integration16

#print axioms GracefulBoundary.Integration16.all_even_ge_16_actual
#print axioms GracefulBoundary.Integration16.all_even_ge_16_unique_zero
