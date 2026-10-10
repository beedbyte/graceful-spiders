import K26Full
namespace GracefulBoundary.FullFixed28
open EvenBoundary.Flexible

def retained4 : List Nat := [15,12,12,13,13]
def seed12 : List Nat := [13,10,9,7,6,4,3,1,0,0,2,3,5,6,8,9,11,11,10,8,7,5,4,2,1]
def graft12 : List Nat := retained4++seed12.tail
theorem retained4_valid : TailGraft.RetainedPrefix 4 12 retained4 := by constructor <;> decide
theorem seed12_core : CorePacket 12 seed12 := by constructor <;> decide
theorem seed12_orientations : seed12[8]?=some 0 ∧ seed12[9]?=some 0 := by decide
theorem graft12_core : CorePacket 14 graft12 := TailGraft.supplied_tail_graft 4 12 (by decide) (by decide) retained4 _ retained4_valid seed12_core
theorem graft12_low : ExtremePacket 14 16 graft12 := by refine ⟨graft12_core,by decide,by decide,?_⟩; intro N; rfl
theorem graft12_high : ExtremePacket 14 15 graft12 := by refine ⟨graft12_core,by decide,by decide,?_⟩; intro N; rfl
theorem k28_depth12 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 28 → Nat, Graceful (spiderGraph n m 28) (n*28+m) f ∧ f (.arm a ⟨11,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 14 n m 16 (by decide) hn graft12 graft12_low a
  exact ⟨f,hf,hz⟩
theorem k28_depth13 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 28 → Nat, Graceful (spiderGraph n m 28) (n*28+m) f ∧ f (.arm a ⟨12,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 14 n m 15 (by decide) hn graft12 graft12_high a
  exact ⟨f,hf,hz⟩

def retained5 : List Nat := [15,12,13,13,11,11,12]
theorem retained5_valid : TailGraft.RetainedPrefix 5 11 retained5 := by constructor <;> decide
def graft11low : List Nat := retained5++FullFixed26.seedLow11.tail
def graft11high : List Nat := retained5++FullFixed26.seedHigh11.tail
theorem graft11low_core : CorePacket 14 graft11low := TailGraft.supplied_tail_graft 5 11 (by decide) (by decide) retained5 _ retained5_valid FullFixed26.seedLow11_core
theorem graft11high_core : CorePacket 14 graft11high := TailGraft.supplied_tail_graft 5 11 (by decide) (by decide) retained5 _ retained5_valid FullFixed26.seedHigh11_core
theorem graft11low_extreme : ExtremePacket 14 14 graft11low := by refine ⟨graft11low_core,by decide,by decide,?_⟩; intro N; rfl
theorem graft11high_extreme : ExtremePacket 14 13 graft11high := by refine ⟨graft11high_core,by decide,by decide,?_⟩; intro N; rfl
theorem k28_depth14 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 28 → Nat, Graceful (spiderGraph n m 28) (n*28+m) f ∧ f (.arm a ⟨13,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 14 n m 14 (by decide) hn graft11low graft11low_extreme a
  exact ⟨f,hf,hz⟩
theorem k28_depth15 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 28 → Nat, Graceful (spiderGraph n m 28) (n*28+m) f ∧ f (.arm a ⟨14,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 14 n m 13 (by decide) hn graft11high graft11high_extreme a
  exact ⟨f,hf,hz⟩

def retained7 : List Nat := [15,12,12,13,13,10,11,11,9,9,10]
theorem retained7_valid : TailGraft.RetainedPrefix 7 9 retained7 := by constructor <;> decide
def graft9low : List Nat := retained7++FullFixed24.seedLow9.tail
def graft9c10 : List Nat := retained7++FullFixed.c10r9.tail
theorem graft9low_core : CorePacket 14 graft9low := TailGraft.supplied_tail_graft 7 9 (by decide) (by decide) retained7 _ retained7_valid FullFixed24.seedLow9_core
theorem graft9c10_core : CorePacket 14 graft9c10 := TailGraft.supplied_tail_graft 7 9 (by decide) (by decide) retained7 _ retained7_valid FullFixed.c10r9_even.core
theorem graft9_c12 : ExtremePacket 14 12 graft9low := by refine ⟨graft9low_core,by decide,by decide,?_⟩; intro N; rfl
theorem graft9_c11 : ExtremePacket 14 11 graft9low := by refine ⟨graft9low_core,by decide,by decide,?_⟩; intro N; rfl
theorem graft9_c10 : ExtremePacket 14 10 graft9c10 := by refine ⟨graft9c10_core,by decide,by decide,?_⟩; intro N; rfl
theorem graft9_c9 : ExtremePacket 14 9 graft9c10 := by refine ⟨graft9c10_core,by decide,by decide,?_⟩; intro N; rfl
theorem k28_depth16 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 28 → Nat, Graceful (spiderGraph n m 28) (n*28+m) f ∧ f (.arm a ⟨15,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 14 n m 12 (by decide) hn graft9low graft9_c12 a
  exact ⟨f,hf,hz⟩
theorem k28_depth17 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 28 → Nat, Graceful (spiderGraph n m 28) (n*28+m) f ∧ f (.arm a ⟨16,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 14 n m 11 (by decide) hn graft9low graft9_c11 a
  exact ⟨f,hf,hz⟩
theorem k28_depth18 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 28 → Nat, Graceful (spiderGraph n m 28) (n*28+m) f ∧ f (.arm a ⟨17,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 14 n m 10 (by decide) hn graft9c10 graft9_c10 a
  exact ⟨f,hf,hz⟩
theorem k28_depth19 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 28 → Nat, Graceful (spiderGraph n m 28) (n*28+m) f ∧ f (.arm a ⟨18,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 14 n m 9 (by decide) hn graft9c10 graft9_c9 a
  exact ⟨f,hf,hz⟩

def tip28 : List Nat := [14,13,13,12,12,11,11,10,10,9,9,8,8,7,7,6,6,5,5,4,4,3,3,2,2,1,1,0,0]
theorem tip28_core : FullFixed.RootZeroTip.CorePacket 14 tip28 := by constructor <;> decide
theorem tip28_decoded_zero (N : Nat) : (decode N false tip28)[28]?=some 0 := by rfl
theorem k28_tip_zero (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 28 → Nat, Graceful (spiderGraph n m 28) (n*28+m) f ∧ f (.arm a ⟨27,by decide⟩)=0 :=
  FullFixed.supplied_tip_zero 14 n m (by decide) (by omega) tip28 tip28_core tip28_decoded_zero a

end GracefulBoundary.FullFixed28
