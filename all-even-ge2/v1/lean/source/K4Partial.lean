import EvenTransfer
import CenterBoundary
import UniversalTip

namespace GracefulBoundary.K4Partial

def path : List Nat := [1,8,0,6,4,5,2,7,3]

theorem path_certificate : Even.Certificate 0 2 3 path := by
  unfold Even.Certificate Even.GenericPathCertificate path
  decide

theorem depth_two_three (n m : Nat) (hn : 2 ≤ n) (a : Fin n) :
    (∃ f : SpiderVertex n m 4 → Nat,
      Graceful (spiderGraph n m 4) (n*4+m) f ∧
      f (.arm a ⟨1,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 4 → Nat,
      Graceful (spiderGraph n m 4) (n*4+m) f ∧
      f (.arm a ⟨2,by decide⟩)=0) := by
  simpa using Even.prescribed_zero 0 2 3 n m path path_certificate hn a

theorem center_zero (n m : Nat) :
    ∃ f : SpiderVertex n m 4 → Nat,
      Graceful (spiderGraph n m 4) (n*4+m) f ∧ f .center=0 := by
  simpa using FullFixed.center_zero 2 n m (by decide)

theorem short_leaf_zero (n m : Nat) (a : Fin m) :
    ∃ f : SpiderVertex n m 4 → Nat,
      Graceful (spiderGraph n m 4) (n*4+m) f ∧ f (.leaf a)=0 := by
  simpa using FullFixed.short_leaf_zero 2 n m (by decide) a

theorem tip_zero (n m : Nat) (hn : 2 ≤ n) (a : Fin n) :
    ∃ f : SpiderVertex n m 4 → Nat,
      Graceful (spiderGraph n m 4) (n*4+m) f ∧ f (.arm a ⟨3,by decide⟩)=0 := by
  simpa using LowBand.actual_tip_zero 2 n m (by decide) (by omega) a

end GracefulBoundary.K4Partial

#print axioms GracefulBoundary.K4Partial.path_certificate
#print axioms GracefulBoundary.K4Partial.depth_two_three
#print axioms GracefulBoundary.K4Partial.center_zero
#print axioms GracefulBoundary.K4Partial.short_leaf_zero
#print axioms GracefulBoundary.K4Partial.tip_zero
