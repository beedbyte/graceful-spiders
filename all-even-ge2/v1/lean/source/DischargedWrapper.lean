import InteriorWrapper
import OddSourceBridge
namespace GracefulBoundary.LowBand
open EvenBoundary

/-- Actual interior graph theorem; only the separately replayed numeric D8 bound is supplied. -/
theorem all_interior_if_D8 (R n m : Nat) (hR : 18≤R) (hn : 2≤n)
    (hD : R≤GapFill.depthPrefix (2*R)) :
    ∀(a : Fin n)(d : Nat),2≤d → d<2*R → NamedDepthZero R n m d a :=
  all_interior R n m hR hn hD all_odd_source_shells

/-- All actual named vertices; each target receives its own labeling. -/
theorem full_actual_if_D8 (R n m : Nat) (hR : 18≤R) (hn : 2≤n)
    (hD : R≤GapFill.depthPrefix (2*R)) (v : SpiderVertex n m (2*R)) :
    ∃f : SpiderVertex n m (2*R) → Nat, Graceful (spiderGraph n m (2*R)) (n*(2*R)+m) f ∧ f v=0 :=
  full_actual_if_sources_and_D8 R n m hR hn hD all_odd_source_shells v

theorem full_unique_zero_if_D8 (R n m : Nat) (hR : 18≤R) (hn : 2≤n)
    (hD : R≤GapFill.depthPrefix (2*R)) (v : SpiderVertex n m (2*R)) :
    ∃f : SpiderVertex n m (2*R) → Nat, Graceful (spiderGraph n m (2*R)) (n*(2*R)+m) f ∧
      f v=0 ∧ ∀w,w≠v → 0<f w := by
  obtain ⟨f,hf,hzero⟩ := full_actual_if_D8 R n m hR hn hD v
  refine ⟨f,hf,hzero,?_⟩
  intro w hw
  have nonzero : f w≠0 := by
    intro hz
    exact hw (hf.vertices.injective w v (hz.trans hzero.symm))
  omega

end GracefulBoundary.LowBand
