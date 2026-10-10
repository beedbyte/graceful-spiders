import ScatteredTheorem
namespace GracefulBoundary.FullFixed30
open EvenBoundary.Flexible

def direct15 : List Nat := [16,13,14,14,12,10,9,7,6,4,3,1,0,0,2,3,5,6,8,9,11,12,13,11,10,8,7,5,4,2,1]
theorem direct15_core : CorePacket 15 direct15 := by constructor <;> decide
theorem direct15_low : ExtremePacket 15 18 direct15 := by refine ⟨direct15_core,by decide,by decide,?_⟩; intro N; rfl
theorem direct15_high : ExtremePacket 15 17 direct15 := by refine ⟨direct15_core,by decide,by decide,?_⟩; intro N; rfl
theorem direct15_orientations : direct15[12]?=some 0 ∧ direct15[13]?=some 0 := by decide

def prefix9 : List Nat := [16,13,14,14,12,12,13,10,11,11,9,9,10]
def prefix11 : List Nat := [16,13,13,14,14,11,11,12,12]
def prefix12 : List Nat := [16,13,14,14,12,12,13]
theorem prefix9_valid : TailGraft.RetainedPrefix 8 9 prefix9 := by constructor <;> decide
theorem prefix11_valid : TailGraft.RetainedPrefix 6 11 prefix11 := by constructor <;> decide
theorem prefix12_valid : TailGraft.RetainedPrefix 5 12 prefix12 := by constructor <;> decide

theorem k30_packet_band (deficit : Nat) (hd : 9≤deficit ∧ deficit≤18) : ∃c,ExtremePacket 15 deficit c := by
  have cases : deficit=9 ∨ deficit=10 ∨ deficit=11 ∨ deficit=12 ∨ deficit=13 ∨ deficit=14 ∨ deficit=15 ∨ deficit=16 ∨ deficit=17 ∨ deficit=18 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|h <;> subst deficit
  · exact ⟨_,Scattered.supplied_extreme_graft 8 9 9 (by decide) (by decide) prefix9 _ prefix9_valid FullFixed.c10r9_odd⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 8 9 10 (by decide) (by decide) prefix9 _ prefix9_valid FullFixed.c10r9_even⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 8 9 11 (by decide) (by decide) prefix9 _ prefix9_valid FullFixed26.low9_c11⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 8 9 12 (by decide) (by decide) prefix9 _ prefix9_valid FullFixed26.low9_c12⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 6 11 13 (by decide) (by decide) prefix11 _ prefix11_valid Scattered.q11_high13⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 6 11 14 (by decide) (by decide) prefix11 _ prefix11_valid Scattered.q11_low14⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 5 12 15 (by decide) (by decide) prefix12 _ prefix12_valid Scattered.q12_high15⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 5 12 16 (by decide) (by decide) prefix12 _ prefix12_valid Scattered.q12_low16⟩
  · exact ⟨direct15,direct15_high⟩
  · exact ⟨direct15,direct15_low⟩

theorem k30_depth12 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 30 → Nat, Graceful (spiderGraph n m 30) (n*30+m) f ∧ f (.arm a ⟨11,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 15 n m 18 (by decide) hn direct15 direct15_low a
  exact ⟨f,hf,hz⟩
theorem k30_depth13 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 30 → Nat, Graceful (spiderGraph n m 30) (n*30+m) f ∧ f (.arm a ⟨12,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 15 n m 17 (by decide) hn direct15 direct15_high a
  exact ⟨f,hf,hz⟩

theorem tip30_core : FullFixed.RootZeroTip.CorePacket 15 (Scattered.tipList 15) := by constructor <;> decide
theorem tip30_zero (N : Nat) : (decode N false (Scattered.tipList 15))[30]?=some 0 := by rfl
theorem k30_tip_zero (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 30 → Nat, Graceful (spiderGraph n m 30) (n*30+m) f ∧ f (.arm a ⟨29,by decide⟩)=0 :=
  FullFixed.supplied_tip_zero 15 n m (by decide) (by omega) (Scattered.tipList 15) tip30_core tip30_zero a

end GracefulBoundary.FullFixed30
