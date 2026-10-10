import FullRotatable
import EvenTransfer

namespace GracefulBoundary.K18
open Even FullFixed

def c2 : List Nat := [3,0,0,1,1,4,2,2,6,6,5,5,4,3]
def c4 : List Nat := [3,1,0,0,2,4,1,2,6,6,5,5,4,3]
def c5 : List Nat := [3,2,1,1,0,0,4,4,2,5,5,6,6,3]
def c7 : List Nat := [3,1,2,4,1,0,0,2,6,6,5,5,4,3]

theorem boundary2 : BoundaryCore 7 c2 := by unfold BoundaryCore; decide
theorem boundary4 : BoundaryCore 7 c4 := by unfold BoundaryCore; decide
theorem boundary5 : BoundaryCore 7 c5 := by unfold BoundaryCore; decide
theorem boundary7 : BoundaryCore 7 c7 := by unfold BoundaryCore; decide

theorem cert2 : Even.Certificate 7 2 3 (Even.completePath 7 c2) := by
  refine ⟨by decide,by decide,by decide,by decide,Even.boundary_shell_bridge 7 c2 boundary2,by decide,by decide⟩
theorem cert4 : Even.Certificate 7 4 3 (Even.completePath 7 c4) := by
  refine ⟨by decide,by decide,by decide,by decide,Even.boundary_shell_bridge 7 c4 boundary4,by decide,by decide⟩
theorem cert5 : Even.Certificate 7 6 5 (Even.completePath 7 c5) := by
  refine ⟨by decide,by decide,by decide,by decide,Even.boundary_shell_bridge 7 c5 boundary5,by decide,by decide⟩
theorem cert7 : Even.Certificate 7 6 7 (Even.completePath 7 c7) := by
  refine ⟨by decide,by decide,by decide,by decide,Even.boundary_shell_bridge 7 c7 boundary7,by decide,by decide⟩

theorem depth2 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 18 → Nat, Graceful (spiderGraph n m 18) (n*18+m) f ∧
      f (.arm a ⟨1,by decide⟩)=0 := (Even.prescribed_zero 7 2 3 n m _ cert2 hn a).1
theorem depth3 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 18 → Nat, Graceful (spiderGraph n m 18) (n*18+m) f ∧
      f (.arm a ⟨2,by decide⟩)=0 := (Even.prescribed_zero 7 2 3 n m _ cert2 hn a).2
theorem depth4 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 18 → Nat, Graceful (spiderGraph n m 18) (n*18+m) f ∧
      f (.arm a ⟨3,by decide⟩)=0 := (Even.prescribed_zero 7 4 3 n m _ cert4 hn a).1
theorem depth5 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 18 → Nat, Graceful (spiderGraph n m 18) (n*18+m) f ∧
      f (.arm a ⟨4,by decide⟩)=0 := (Even.prescribed_zero 7 6 5 n m _ cert5 hn a).2
theorem depth6 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 18 → Nat, Graceful (spiderGraph n m 18) (n*18+m) f ∧
      f (.arm a ⟨5,by decide⟩)=0 := (Even.prescribed_zero 7 6 5 n m _ cert5 hn a).1
theorem depth7 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 18 → Nat, Graceful (spiderGraph n m 18) (n*18+m) f ∧
      f (.arm a ⟨6,by decide⟩)=0 := (Even.prescribed_zero 7 6 7 n m _ cert7 hn a).2

end GracefulBoundary.K18
