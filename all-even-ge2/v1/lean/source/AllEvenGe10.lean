import K10Independent
import AllEvenGe12

namespace GracefulBoundary.Integration10

/-- Every actual named vertex of the spider has its own graceful zero labeling
    for every even arm length at least ten. -/
theorem all_even_ge_10_actual (k n m : Nat) (hk : 10 ≤ k)
    (heven : k % 2 = 0) (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f v = 0 := by
  by_cases h10 : k = 10
  · subst k
    exact K10Independent.full_actual n m hn v
  · exact Integration12.all_even_ge_12_actual k n m (by omega) heven hn v

theorem all_even_ge_10_unique_zero (k n m : Nat) (hk : 10 ≤ k)
    (heven : k % 2 = 0) (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧
      f v = 0 ∧ ∀ w, w ≠ v → 0 < f w := by
  obtain ⟨f,hf,hz⟩ := all_even_ge_10_actual k n m hk heven hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have hnonzero : f w ≠ 0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.Integration10

#print axioms GracefulBoundary.Integration10.all_even_ge_10_actual
#print axioms GracefulBoundary.Integration10.all_even_ge_10_unique_zero
