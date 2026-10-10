import K4RootOne

namespace GracefulBoundary.Integration4

/-- The full named-vertex k=4 theorem, conditional only on the exact
    root-one base inventory isolated in K4RootOne.lean. -/
theorem k4_actual_of_base (hbase : K4RootOne.BaseGracefulness)
    (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 4) :
    ∃ f : SpiderVertex n m 4 → Nat,
      Graceful (spiderGraph n m 4) (n*4+m) f ∧ f v=0 := by
  cases v with
  | center => exact K4Partial.center_zero n m
  | leaf a => exact K4Partial.short_leaf_zero n m a
  | arm a d =>
    have hd : d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 := by
      have := d.isLt
      omega
    rcases hd with h0|h1|h2|h3
    · have hd0 : d=⟨0,by decide⟩ := Fin.ext h0
      subst d
      exact K4RootOne.depth_one_of_base hbase n m hn a
    · have hd1 : d=⟨1,by decide⟩ := Fin.ext h1
      subst d
      exact (K4Partial.depth_two_three n m hn a).1
    · have hd2 : d=⟨2,by decide⟩ := Fin.ext h2
      subst d
      exact (K4Partial.depth_two_three n m hn a).2
    · have hd3 : d=⟨3,by decide⟩ := Fin.ext h3
      subst d
      exact K4Partial.tip_zero n m hn a

/-- Even lengths at least four, conditional solely on the new k=4 base
    inventory; the previously replayed ≥6 theorem is imported unchanged. -/
theorem all_even_ge_4_actual_of_base (hbase : K4RootOne.BaseGracefulness)
    (k n m : Nat) (hk : 4 ≤ k) (heven : k % 2=0)
    (hn : 2 ≤ n) (v : SpiderVertex n m k) :
    ∃ f : SpiderVertex n m k → Nat,
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f v=0 := by
  by_cases h4 : k=4
  · subst k
    exact k4_actual_of_base hbase n m hn v
  exact Integration6.all_even_ge_6_actual k n m (by omega) heven hn v

end GracefulBoundary.Integration4

#print axioms GracefulBoundary.Integration4.k4_actual_of_base
#print axioms GracefulBoundary.Integration4.all_even_ge_4_actual_of_base
