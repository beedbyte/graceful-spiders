import GraphComplement
namespace GracefulBoundary.EvenBoundary.Flexible

def extremeValue (N deficit : Nat) : Nat := if deficit%2=0 then 0 else N

structure ExtremePacket (r deficit : Nat) (c : List Nat) : Prop where
  core : CorePacket r c
  depthPositive : 1≤2*r-deficit
  zeroOffset : c[2*r-deficit]?=some 0
  decodedExtreme : ∀N,(decode N false c)[2*r-deficit]?=some (extremeValue N deficit)

def s52 : List Nat := [6,3,2,1,3,4,4,2,0,0,1]
def s62 : List Nat := [7,4,3,1,2,3,5,5,4,2,0,0,1]
def s54alt : List Nat := [6,3,4,4,2,0,0,1,3,2,1]
def s68 : List Nat := [7,4,3,1,0,0,2,3,5,5,4,2,1]
def s98 : List Nat := [10,7,6,6,8,8,7,4,3,1,0,0,2,3,5,5,4,2,1]

theorem s52_c1 : ExtremePacket 5 1 s52 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s52_c2 : ExtremePacket 5 2 s52 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s62_c1 : ExtremePacket 6 1 s62 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s62_c2 : ExtremePacket 6 2 s62 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s54_c3 : ExtremePacket 5 3 c4r5 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s54_c4 : ExtremePacket 5 4 c4r5 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s64_c3 : ExtremePacket 6 3 c4r6 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s64_c4 : ExtremePacket 6 4 c4r6 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s54alt_c5 : ExtremePacket 5 5 s54alt := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s66_c5 : ExtremePacket 6 5 c6r6 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s56_c6 : ExtremePacket 5 6 c6r5 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s66_c6 : ExtremePacket 6 6 c6r6 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s56_c7 : ExtremePacket 5 7 c6r5 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s68_c7 : ExtremePacket 6 7 s68 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s68_c8 : ExtremePacket 6 8 s68 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem s98_c8 : ExtremePacket 9 8 s98 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)

theorem extreme_packet_step (r deficit : Nat) (c : List Nat) (hc : ExtremePacket r deficit c) :
    ExtremePacket (r+2) deficit (LabelOne.step r c) := by
  have positive := hc.depthPositive
  have index : 2*(r+2)-deficit=4+(2*r-deficit) := by omega
  refine ⟨core_step r c hc.core,by omega,?_,?_⟩
  · rw [LabelOne.step,index,List.getElem?_append_right (by simp)]
    simpa using hc.zeroOffset
  · intro N
    change ([r+3,N-r,r,N-(r+1)]++decode N false c)[2*(r+2)-deficit]?=some (extremeValue N deficit)
    rw [index,List.getElem?_append_right (by simp)]
    simpa using hc.decodedExtreme N

theorem extreme_base_even (deficit : Nat) (hd : 1≤deficit ∧ deficit≤8) : ∃c,ExtremePacket 8 deficit c := by
  have lift {c : List Nat} : ExtremePacket 6 deficit c → ∃d,ExtremePacket 8 deficit d := fun hc => ⟨_,extreme_packet_step 6 deficit c hc⟩
  have cases : deficit=1 ∨ deficit=2 ∨ deficit=3 ∨ deficit=4 ∨ deficit=5 ∨ deficit=6 ∨ deficit=7 ∨ deficit=8 := by omega
  rcases cases with h|h|h|h|h|h|h|h <;> subst deficit
  · exact lift s62_c1
  · exact lift s62_c2
  · exact lift s64_c3
  · exact lift s64_c4
  · exact lift s66_c5
  · exact lift s66_c6
  · exact lift s68_c7
  · exact lift s68_c8

theorem extreme_base_odd (deficit : Nat) (hd : 1≤deficit ∧ deficit≤8) : ∃c,ExtremePacket 9 deficit c := by
  have lift {c : List Nat} : ExtremePacket 5 deficit c → ∃d,ExtremePacket 9 deficit d :=
    fun hc => ⟨_,extreme_packet_step 7 deficit _ (extreme_packet_step 5 deficit c hc)⟩
  have cases : deficit=1 ∨ deficit=2 ∨ deficit=3 ∨ deficit=4 ∨ deficit=5 ∨ deficit=6 ∨ deficit=7 ∨ deficit=8 := by omega
  rcases cases with h|h|h|h|h|h|h|h <;> subst deficit
  · exact lift s52_c1
  · exact lift s52_c2
  · exact lift s54_c3
  · exact lift s54_c4
  · exact lift s54alt_c5
  · exact lift s56_c6
  · exact lift s56_c7
  · exact ⟨_,s98_c8⟩

theorem all_eight_extreme_packets (r deficit : Nat) (hr : 8≤r) (hd : 1≤deficit ∧ deficit≤8) :
    ∃c,ExtremePacket r deficit c := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    by_cases eight : r=8
    · subst r; exact extreme_base_even deficit hd
    by_cases nine : r=9
    · subst r; exact extreme_base_odd deficit hd
    obtain ⟨c,hc⟩ := ih (r-2) (by omega) (by omega)
    have size : r-2+2=r := by omega
    simpa only [size] using (show ∃d,ExtremePacket (r-2+2) deficit d from ⟨_,extreme_packet_step (r-2) deficit c hc⟩)

theorem extreme_packet_attachment {W E : Type} (H : IndexedGraph W E) (root : W) (Q r deficit : Nat)
    (c : List Nat) (hc : ExtremePacket r deficit c) (g : W → Nat) (hg : Graceful H Q g) (hroot : g root=1) :
    ∃f : Sum W (Fin (2*r)) → Nat, Graceful (graph H root r) (Q+2*r) f ∧
      f (.inr ⟨2*r-deficit-1,by have := hc.depthPositive; omega⟩)=extremeValue (Q+2*r) deficit := by
  refine ⟨label Q r c g,packet_attachment_graceful H root Q r c hc.core g hg hroot,?_⟩
  have target := hc.decodedExtreme (Q+2*r)
  rw [decoded_first Q r c hc.core] at target
  have index : 2*r-deficit=(2*r-deficit-1)+1 := by have := hc.depthPositive; omega
  rw [index,List.getElem?_cons_succ] at target
  dsimp only [label]
  rw [List.getD_eq_getElem?_getD,target]
  rfl

end GracefulBoundary.EvenBoundary.Flexible
