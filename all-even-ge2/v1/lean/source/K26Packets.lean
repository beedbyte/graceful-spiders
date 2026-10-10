import K24Full
namespace GracefulBoundary.FullFixed26
open EvenBoundary.Flexible

def retained4 : List Nat := [14,11,11,12,12]
def seedLow11 : List Nat := [12,9,8,6,5,3,2,0,0,1,3,4,6,7,9,10,10,8,7,5,4,2,1]
def seedHigh11 : List Nat := [12,9,10,10,8,6,5,3,2,0,0,1,3,4,6,7,9,8,7,5,4,2,1]
def graftLow : List Nat := retained4++seedLow11.tail
def graftHigh : List Nat := retained4++seedHigh11.tail
theorem q11_distinct_orientations : seedLow11≠seedHigh11 ∧ seedLow11[8]?=some 0 ∧ seedLow11[9]?=some 1 ∧ seedHigh11[8]?=some 2 ∧ seedHigh11[9]?=some 0 := by decide
theorem retained4_valid : TailGraft.RetainedPrefix 4 11 retained4 := by constructor <;> decide
theorem seedLow11_core : CorePacket 11 seedLow11 := by constructor <;> decide
theorem seedHigh11_core : CorePacket 11 seedHigh11 := by constructor <;> decide
theorem graftLow_core : CorePacket 13 graftLow := TailGraft.supplied_tail_graft 4 11 (by decide) (by decide) retained4 _ retained4_valid seedLow11_core
theorem graftHigh_core : CorePacket 13 graftHigh := TailGraft.supplied_tail_graft 4 11 (by decide) (by decide) retained4 _ retained4_valid seedHigh11_core
theorem graftLow_extreme : ExtremePacket 13 14 graftLow := by refine ⟨graftLow_core,by decide,by decide,?_⟩; intro N; rfl
theorem graftHigh_extreme : ExtremePacket 13 13 graftHigh := by refine ⟨graftHigh_core,by decide,by decide,?_⟩; intro N; rfl
theorem k26_depth12 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 26 → Nat, Graceful (spiderGraph n m 26) (n*26+m) f ∧ f (.arm a ⟨11,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 13 n m 14 (by decide) hn graftLow graftLow_extreme a
  exact ⟨f,hf,hz⟩
theorem k26_depth13 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 26 → Nat, Graceful (spiderGraph n m 26) (n*26+m) f ∧ f (.arm a ⟨12,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 13 n m 13 (by decide) hn graftHigh graftHigh_extreme a
  exact ⟨f,hf,hz⟩

theorem low9_c12 : ExtremePacket 9 12 FullFixed24.seedLow9 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem low9_c11 : ExtremePacket 9 11 FullFixed24.seedLow9 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem k26_depth14 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 26 → Nat, Graceful (spiderGraph n m 26) (n*26+m) f ∧ f (.arm a ⟨13,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 13 n m 12 (by decide) hn _
    (extreme_packet_step 11 12 _ (extreme_packet_step 9 12 _ low9_c12)) a
  exact ⟨f,hf,hz⟩
theorem k26_depth15 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 26 → Nat, Graceful (spiderGraph n m 26) (n*26+m) f ∧ f (.arm a ⟨14,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 13 n m 11 (by decide) hn _
    (extreme_packet_step 11 11 _ (extreme_packet_step 9 11 _ low9_c11)) a
  exact ⟨f,hf,hz⟩
theorem k26_depth16 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 26 → Nat, Graceful (spiderGraph n m 26) (n*26+m) f ∧ f (.arm a ⟨15,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 13 n m 10 (by decide) hn _
    (extreme_packet_step 11 10 _ (extreme_packet_step 9 10 _ FullFixed.c10r9_even)) a
  exact ⟨f,hf,hz⟩
theorem k26_depth17 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 26 → Nat, Graceful (spiderGraph n m 26) (n*26+m) f ∧ f (.arm a ⟨16,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 13 n m 9 (by decide) hn _
    (extreme_packet_step 11 9 _ (extreme_packet_step 9 9 _ FullFixed.c10r9_odd)) a
  exact ⟨f,hf,hz⟩

def tip26 : List Nat := [13,12,12,11,11,10,10,9,9,8,8,7,7,6,6,5,5,4,4,3,3,2,2,1,1,0,0]
theorem tip26_core : FullFixed.RootZeroTip.CorePacket 13 tip26 := by constructor <;> decide
theorem tip26_decoded_zero (N : Nat) : (decode N false tip26)[26]?=some 0 := by rfl
theorem k26_tip_zero (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 26 → Nat, Graceful (spiderGraph n m 26) (n*26+m) f ∧ f (.arm a ⟨25,by decide⟩)=0 :=
  FullFixed.supplied_tip_zero 13 n m (by decide) (by omega) tip26 tip26_core tip26_decoded_zero a

end GracefulBoundary.FullFixed26
