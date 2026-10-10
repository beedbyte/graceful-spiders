import K2Actual
import AllEvenGe4

namespace GracefulBoundary.Integration2

/-- Exact even k>=2 all-vertex theorem, conditional on the single open k=4
    source inventory. No unproved prerequisite is hidden. -/
theorem all_even_ge_2_actual_of_k4_base
    (hbase : K4RootOne.BaseGracefulness)
    (k n m : Nat) (hk : 2≤k) (heven : k%2=0)
    (hn : 2≤n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f v=0 := by
  by_cases h2 : k=2
  · subst k
    exact K2Actual.full_actual n m hn v
  by_cases h4 : k=4
  · subst k
    exact Integration4.k4_actual_of_base hbase n m hn v
  exact Integration6.all_even_ge_6_actual k n m (by omega) heven hn v

theorem all_even_ge_2_unique_zero_of_k4_base
    (hbase : K4RootOne.BaseGracefulness)
    (k n m : Nat) (hk : 2≤k) (heven : k%2=0)
    (hn : 2≤n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧
      f v=0 ∧ ∀w,w≠v → 0<f w := by
  obtain ⟨f,hf,hz⟩ := all_even_ge_2_actual_of_k4_base hbase k n m hk heven hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have hne : f w≠0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.Integration2

#print axioms GracefulBoundary.Integration2.all_even_ge_2_actual_of_k4_base
#print axioms GracefulBoundary.Integration2.all_even_ge_2_unique_zero_of_k4_base
