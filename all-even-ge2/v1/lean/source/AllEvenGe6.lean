import K6Existing
import K8Fixed
import AllEvenGe10

namespace GracefulBoundary.Integration6

/-- Every actual named vertex of the spider has its own graceful zero labeling
    for every even arm length at least six. -/
theorem all_even_ge_6_actual (k n m : Nat) (hk : 6 ≤ k)
    (heven : k % 2 = 0) (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f v = 0 := by
  by_cases h6 : k = 6
  · subst k
    exact K6Existing.full_actual n m hn v
  by_cases h8 : k = 8
  · subst k
    exact K8Fixed.full_actual n m hn v
  exact Integration10.all_even_ge_10_actual k n m (by omega) heven hn v

theorem all_even_ge_6_unique_zero (k n m : Nat) (hk : 6 ≤ k)
    (heven : k % 2 = 0) (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧
      f v = 0 ∧ ∀ w, w ≠ v → 0 < f w := by
  obtain ⟨f,hf,hz⟩ := all_even_ge_6_actual k n m hk heven hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have hnonzero : f w ≠ 0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.Integration6

#print axioms GracefulBoundary.Integration6.all_even_ge_6_actual
#print axioms GracefulBoundary.Integration6.all_even_ge_6_unique_zero
