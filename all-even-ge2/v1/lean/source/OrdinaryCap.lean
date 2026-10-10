import Deficit24Composition
namespace GracefulBoundary.OrdinaryPhase
open EvenBoundary.Flexible

structure Cap (r : Nat) (c : List Nat) : Prop where
  core : CorePacket r c
  firstHigh : c[1]?=some (r-2)
  last : c.getLast?=some 1

def H3 : List Nat := [4,1,2,2,0,0,1]
def H4 : List Nat := [5,2,2,3,3,0,0,1,1]
theorem H3_valid : Cap 3 H3 := by
  refine ⟨?_,by decide,by decide⟩
  constructor <;> decide
theorem H4_valid : Cap 4 H4 := by
  refine ⟨?_,by decide,by decide⟩
  constructor <;> decide

theorem cap_step (r : Nat) (c : List Nat) (hc : Cap r c) : Cap (r+2) (LabelOne.step r c) := by
  refine ⟨core_step r c hc.core,?_,?_⟩
  · simp [LabelOne.step]
  · change ([r+3,r,r,r+1]++c).getLast?=some 1
    rw [List.getLast?_append,hc.last]; rfl

theorem caps : ∀r,3≤r → ∃c,Cap r c := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro hr
    by_cases three : r=3
    · subst r; exact ⟨H3,H3_valid⟩
    by_cases four : r=4
    · subst r; exact ⟨H4,H4_valid⟩
    obtain ⟨c,hc⟩ := ih (r-2) (by omega) (by omega)
    have eq : r-2+2=r := by omega
    simpa only [eq] using (show ∃d,Cap (r-2+2) d from ⟨_,cap_step (r-2) c hc⟩)

end GracefulBoundary.OrdinaryPhase
