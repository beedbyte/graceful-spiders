import K14Independent
import AllEvenGe16

namespace GracefulBoundary.Integration14

/-- Every actual named vertex of the spider has a graceful labeling with zero
    there, for every even arm length at least fourteen. -/
theorem all_even_ge_14_actual (k n m : Nat) (hk : 14 ≤ k)
    (heven : k % 2 = 0) (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f v = 0 := by
  by_cases h14 : k = 14
  · subst k
    exact K14Independent.full_actual n m hn v
  · exact Integration16.all_even_ge_16_actual k n m (by omega) heven hn v

/-- The zero is unique in each selected graceful labeling. -/
theorem all_even_ge_14_unique_zero (k n m : Nat) (hk : 14 ≤ k)
    (heven : k % 2 = 0) (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧
      f v = 0 ∧ ∀ w, w ≠ v → 0 < f w := by
  obtain ⟨f,hf,hz⟩ := all_even_ge_14_actual k n m hk heven hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have hnonzero : f w ≠ 0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.Integration14

#print axioms GracefulBoundary.Integration14.all_even_ge_14_actual
#print axioms GracefulBoundary.Integration14.all_even_ge_14_unique_zero
