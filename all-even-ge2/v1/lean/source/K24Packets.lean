import TailGraftInterface
namespace GracefulBoundary.FullFixed24
open EvenBoundary.Flexible

def retained5 : List Nat := [13,10,11,11,9,9,10]
def seedLow9 : List Nat := [10,7,6,4,3,1,0,0,2,3,5,6,8,8,7,5,4,2,1]
def graftLow : List Nat := retained5++seedLow9.tail
def graftHigh : List Nat := retained5++FullFixed.c10r9.tail
theorem retained5_valid : TailGraft.RetainedPrefix 5 9 retained5 := by constructor <;> decide
theorem seedLow9_core : CorePacket 9 seedLow9 := by constructor <;> decide
theorem graftLow_core : CorePacket 12 graftLow := by
  exact TailGraft.supplied_tail_graft 5 9 (by decide) (by decide) retained5 _ retained5_valid seedLow9_core
theorem graftHigh_core : CorePacket 12 graftHigh := by
  exact TailGraft.supplied_tail_graft 5 9 (by decide) (by decide) retained5 _ retained5_valid FullFixed.c10r9_even.core
theorem graftLow_extreme : ExtremePacket 12 12 graftLow := by
  refine ⟨graftLow_core,by decide,by decide,?_⟩
  intro N; rfl
theorem graftHigh_extreme : ExtremePacket 12 9 graftHigh := by
  refine ⟨graftHigh_core,by decide,by decide,?_⟩
  intro N; rfl

theorem k24_depth12 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 24 → Nat, Graceful (spiderGraph n m 24) (n*24+m) f ∧ f (.arm a ⟨11,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 12 n m 12 (by decide) hn graftLow graftLow_extreme a
  exact ⟨f,hf,hz⟩
theorem k24_depth15 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 24 → Nat, Graceful (spiderGraph n m 24) (n*24+m) f ∧ f (.arm a ⟨14,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 12 n m 9 (by decide) hn graftHigh graftHigh_extreme a
  exact ⟨f,hf,hz⟩

def c10r8 : List Nat := [9,6,5,3,2,0,0,1,3,4,6,7,7,5,4,2,1]
theorem c10r8_low : ExtremePacket 8 10 c10r8 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem c10r8_high : ExtremePacket 8 11 c10r8 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem k24_depth14 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 24 → Nat, Graceful (spiderGraph n m 24) (n*24+m) f ∧ f (.arm a ⟨13,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 12 n m 10 (by decide) hn _
    (extreme_packet_step 10 10 _ (extreme_packet_step 8 10 c10r8 c10r8_low)) a
  exact ⟨f,hf,hz⟩
theorem k24_depth13 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 24 → Nat, Graceful (spiderGraph n m 24) (n*24+m) f ∧ f (.arm a ⟨12,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 12 n m 11 (by decide) hn _
    (extreme_packet_step 10 11 _ (extreme_packet_step 8 11 c10r8 c10r8_high)) a
  exact ⟨f,hf,hz⟩

def tip24 : List Nat := [12,11,11,10,10,9,9,8,8,7,7,6,6,5,5,4,4,3,3,2,2,1,1,0,0]
theorem tip24_core : FullFixed.RootZeroTip.CorePacket 12 tip24 := by constructor <;> decide
theorem tip24_decoded_zero (N : Nat) : (decode N false tip24)[24]?=some 0 := by rfl
theorem k24_tip_zero (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 24 → Nat, Graceful (spiderGraph n m 24) (n*24+m) f ∧ f (.arm a ⟨23,by decide⟩)=0 :=
  FullFixed.supplied_tip_zero 12 n m (by decide) (by omega) tip24 tip24_core tip24_decoded_zero a

end GracefulBoundary.FullFixed24
