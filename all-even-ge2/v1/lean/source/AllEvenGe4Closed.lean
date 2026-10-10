import Inventory
import AllEvenGe4

namespace GracefulBoundary.Integration4Closed

/-- Every actual named vertex of S(4^n,1^m) can be zero. -/
theorem k4_actual (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 4) :
    ∃ f : SpiderVertex n m 4 → Nat,
      Graceful (spiderGraph n m 4) (n*4+m) f ∧ f v=0 :=
  Integration4.k4_actual_of_base K4Inventory.base_gracefulness n m hn v

/-- Unconditional fixed lower bound: every even k≥4, all n≥2,m≥0,
    and every actual named target vertex. -/
theorem all_even_ge_4_actual (k n m : Nat) (hk : 4≤k)
    (heven : k%2=0) (hn : 2≤n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f v=0 :=
  Integration4.all_even_ge_4_actual_of_base
    K4Inventory.base_gracefulness k n m hk heven hn v

end GracefulBoundary.Integration4Closed

#print axioms GracefulBoundary.Integration4Closed.k4_actual
#print axioms GracefulBoundary.Integration4Closed.all_even_ge_4_actual
