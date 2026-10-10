import FlexibleAttachment
namespace GracefulBoundary.EvenBoundary.Flexible

def Deficit (c : Nat) : Prop := c=2 ∨ c=4 ∨ c=6
structure ZeroPacket (r deficit : Nat) (c : List Nat) : Prop where
  core : CorePacket r c
  depthPositive : 1≤2*r-deficit
  zero : c[2*r-deficit]?=some 0
  decodedZero : ∀N,(decode N false c)[2*r-deficit]?=some 0

def c6r5 : List Nat := [6,3,2,0,0,1,3,4,4,2,1]
def c6r6 : List Nat := [7,4,5,5,3,1,0,0,2,3,4,2,1]
def c4r5 : List Nat := [6,3,3,4,4,1,0,0,2,2,1]
def c4r6 : List Nat := [7,4,3,3,5,5,4,1,0,0,2,2,1]

theorem c6r5_valid : ZeroPacket 5 6 c6r5 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem c6r6_valid : ZeroPacket 6 6 c6r6 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem c4r5_valid : ZeroPacket 5 4 c4r5 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem c4r6_valid : ZeroPacket 6 4 c4r6 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)

theorem zero_packet_step (r deficit : Nat) (c : List Nat) (hc : ZeroPacket r deficit c) :
    ZeroPacket (r+2) deficit (LabelOne.step r c) := by
  have positive := hc.depthPositive
  have index : 2*(r+2)-deficit=4+(2*r-deficit) := by omega
  refine ⟨core_step r c hc.core,by omega,?_,?_⟩
  · rw [LabelOne.step,index,List.getElem?_append_right (by simp)]
    simpa using hc.zero
  · intro N
    change ([r+3,N-r,r,N-(r+1)]++decode N false c)[2*(r+2)-deficit]?=some 0
    rw [index,List.getElem?_append_right (by simp)]
    simpa using hc.decodedZero N

theorem c4_packets : ∀r,5≤r → ∃c,ZeroPacket r 4 c := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro hr
    by_cases five : r=5
    · subst r; exact ⟨c4r5,c4r5_valid⟩
    by_cases six : r=6
    · subst r; exact ⟨c4r6,c4r6_valid⟩
    obtain ⟨c,hc⟩ := ih (r-2) (by omega) (by omega)
    have next := zero_packet_step (r-2) 4 c hc
    have size : r-2+2=r := by omega
    simpa only [size] using (show ∃d,ZeroPacket (r-2+2) 4 d from ⟨_,next⟩)

theorem c6_packets : ∀r,5≤r → ∃c,ZeroPacket r 6 c := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro hr
    by_cases five : r=5
    · subst r; exact ⟨c6r5,c6r5_valid⟩
    by_cases six : r=6
    · subst r; exact ⟨c6r6,c6r6_valid⟩
    obtain ⟨c,hc⟩ := ih (r-2) (by omega) (by omega)
    have next := zero_packet_step (r-2) 6 c hc
    have size : r-2+2=r := by omega
    simpa only [size] using (show ∃d,ZeroPacket (r-2+2) 6 d from ⟨_,next⟩)

theorem c2_packets (r : Nat) (hr : 3≤r) : ∃c,ZeroPacket r 2 c := by
  obtain ⟨c,hc⟩ := LabelOne.packets r (by omega)
  exact ⟨c,core_from_packet r c hc,by omega,hc.zero,hc.decodedZero⟩

theorem all_three_packets (r deficit : Nat) (hr : 5≤r) (hd : Deficit deficit) : ∃c,ZeroPacket r deficit c := by
  rcases hd with h|h|h <;> subst deficit
  · exact c2_packets r (by omega)
  · exact c4_packets r hr
  · exact c6_packets r hr

/-- Universal actual graph attachment at a supplied root labeled 1, with the selected packet zero depth. -/
theorem zero_packet_attachment {W E : Type} (H : IndexedGraph W E) (root : W) (Q r deficit : Nat)
    (c : List Nat) (hc : ZeroPacket r deficit c) (g : W → Nat) (hg : Graceful H Q g) (hroot : g root=1) :
    ∃f : Sum W (Fin (2*r)) → Nat, Graceful (graph H root r) (Q+2*r) f ∧
      f (.inr ⟨2*r-deficit-1,by have := hc.depthPositive; omega⟩)=0 := by
  refine ⟨label Q r c g,packet_attachment_graceful H root Q r c hc.core g hg hroot,?_⟩
  have zero := hc.decodedZero (Q+2*r)
  rw [decoded_first Q r c hc.core] at zero
  have index : 2*r-deficit=(2*r-deficit-1)+1 := by have := hc.depthPositive; omega
  rw [index,List.getElem?_cons_succ] at zero
  dsimp only [label]
  rw [List.getD_eq_getElem?_getD,zero]
  rfl

end GracefulBoundary.EvenBoundary.Flexible
