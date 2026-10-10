import AllEvenGe2
import AllEvenGe4Closed

namespace GracefulBoundary.Integration2Closed

/-- Every actual named vertex of S(k^n,1^m) can be zero for every
    even k at least two and every n at least two. -/
theorem all_even_ge_2_actual (k n m : Nat) (hk : 2≤k)
    (heven : k%2=0) (hn : 2≤n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f v=0 :=
  Integration2.all_even_ge_2_actual_of_k4_base
    K4Inventory.base_gracefulness k n m hk heven hn v

theorem all_even_ge_2_unique_zero (k n m : Nat) (hk : 2≤k)
    (heven : k%2=0) (hn : 2≤n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧
      f v=0 ∧ ∀w,w≠v → 0<f w :=
  Integration2.all_even_ge_2_unique_zero_of_k4_base
    K4Inventory.base_gracefulness k n m hk heven hn v

end GracefulBoundary.Integration2Closed

#print axioms GracefulBoundary.Integration2Closed.all_even_ge_2_actual
#print axioms GracefulBoundary.Integration2Closed.all_even_ge_2_unique_zero
