import K12Independent
import AllEvenGe14

namespace GracefulBoundary.Integration12

/-- Every actual named vertex of the spider has its own graceful zero labeling
    for every even arm length at least twelve. -/
theorem all_even_ge_12_actual (k n m : Nat) (hk : 12 ≤ k)
    (heven : k % 2 = 0) (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f v = 0 := by
  by_cases h12 : k = 12
  · subst k
    exact K12Independent.full_actual n m hn v
  · exact Integration14.all_even_ge_14_actual k n m (by omega) heven hn v

theorem all_even_ge_12_unique_zero (k n m : Nat) (hk : 12 ≤ k)
    (heven : k % 2 = 0) (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧
      f v = 0 ∧ ∀ w, w ≠ v → 0 < f w := by
  obtain ⟨f,hf,hz⟩ := all_even_ge_12_actual k n m hk heven hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have hnonzero : f w ≠ 0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.Integration12

#print axioms GracefulBoundary.Integration12.all_even_ge_12_actual
#print axioms GracefulBoundary.Integration12.all_even_ge_12_unique_zero
