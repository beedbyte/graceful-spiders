import K34Full
namespace GracefulBoundary.Deficit24
open EvenBoundary.Flexible

def q15 : List Nat := [16, 13, 14, 14, 12, 10, 9, 7, 6, 4, 3, 1, 0, 0, 2, 3, 5, 6, 8, 9, 11, 12, 13, 11, 10, 8, 7, 5, 4, 2, 1]
theorem q15_core : CorePacket 15 q15 := by constructor <;> decide
theorem q15_c17 : ExtremePacket 15 17 q15 := by refine ⟨q15_core,by decide,by decide,?_⟩; intro N; rfl
theorem q15_c18 : ExtremePacket 15 18 q15 := by refine ⟨q15_core,by decide,by decide,?_⟩; intro N; rfl
def q17 : List Nat := [18, 15, 15, 16, 16, 13, 12, 10, 9, 7, 6, 4, 3, 1, 0, 0, 2, 3, 5, 6, 8, 9, 11, 12, 14, 14, 13, 11, 10, 8, 7, 5, 4, 2, 1]
theorem q17_core : CorePacket 17 q17 := by constructor <;> decide
theorem q17_c19 : ExtremePacket 17 19 q17 := by refine ⟨q17_core,by decide,by decide,?_⟩; intro N; rfl
theorem q17_c20 : ExtremePacket 17 20 q17 := by refine ⟨q17_core,by decide,by decide,?_⟩; intro N; rfl
def q21late : List Nat := [22, 19, 20, 20, 18, 16, 17, 18, 19, 17, 15, 13, 12, 10, 9, 7, 6, 4, 3, 1, 0, 0, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15, 16, 14, 13, 11, 10, 8, 7, 5, 4, 2, 1]
theorem q21late_core : CorePacket 21 q21late := by constructor <;> decide
theorem q21late_c21 : ExtremePacket 21 21 q21late := by refine ⟨q21late_core,by decide,by decide,?_⟩; intro N; rfl
theorem q21late_c22 : ExtremePacket 21 22 q21late := by refine ⟨q21late_core,by decide,by decide,?_⟩; intro N; rfl
def q21early : List Nat := [22, 19, 18, 18, 20, 20, 19, 16, 15, 13, 12, 10, 9, 7, 6, 4, 3, 1, 0, 0, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15, 17, 17, 16, 14, 13, 11, 10, 8, 7, 5, 4, 2, 1]
theorem q21early_core : CorePacket 21 q21early := by constructor <;> decide
theorem q21early_c23 : ExtremePacket 21 23 q21early := by refine ⟨q21early_core,by decide,by decide,?_⟩; intro N; rfl
theorem q21early_c24 : ExtremePacket 21 24 q21early := by refine ⟨q21early_core,by decide,by decide,?_⟩; intro N; rfl

/-- Supplied retained-prefix contract, all target radii; no canonical existence is assumed. -/
theorem symbolic_graft (R q c : Nat) (hr : q+2≤R) (hq : 2≤q) (p u : List Nat)
    (hp : TailGraft.RetainedPrefix (R-q+2) q p)
    (hu : ExtremePacket q c ((q+1)::(q-2)::u)) : ∃v,ExtremePacket R c v := by
  have graft := Scattered.supplied_extreme_graft (R-q+2) q c (by omega) hq p u hp hu
  have size : R-q+2+q-2=R := by omega
  simpa only [size] using (show ∃v,ExtremePacket (R-q+2+q-2) c v from ⟨_,graft⟩)

theorem deficit_preserved (r q c : Nat) (hr : 4≤r) (hd : c≤2*q) :
    2*(r+q-2)-c=(2*q-c)+(2*r-4) := by omega

end GracefulBoundary.Deficit24
