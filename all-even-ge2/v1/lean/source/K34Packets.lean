import K34Certificates
namespace GracefulBoundary.FullFixed34
open EvenBoundary.Flexible

def prefix9 : List Nat := [18, 15, 15, 16, 16, 13, 14, 14, 12, 12, 13, 10, 11, 11, 9, 9, 10]
theorem prefix9_valid : TailGraft.RetainedPrefix 10 9 prefix9 := by constructor <;> decide
def prefix11 : List Nat := [18, 15, 16, 16, 14, 14, 15, 12, 13, 13, 11, 11, 12]
theorem prefix11_valid : TailGraft.RetainedPrefix 8 11 prefix11 := by constructor <;> decide
def prefix12 : List Nat := [18, 15, 15, 16, 16, 13, 14, 14, 12, 12, 13]
theorem prefix12_valid : TailGraft.RetainedPrefix 7 12 prefix12 := by constructor <;> decide
def prefix15 : List Nat := [18, 15, 15, 16, 16]
theorem prefix15_valid : TailGraft.RetainedPrefix 4 15 prefix15 := by constructor <;> decide

theorem k34_packet_band (deficit : Nat) (hd : 9≤deficit ∧ deficit≤18) : ∃c,ExtremePacket 17 deficit c := by
  have cases : deficit=9 ∨ deficit=10 ∨ deficit=11 ∨ deficit=12 ∨ deficit=13 ∨ deficit=14 ∨ deficit=15 ∨ deficit=16 ∨ deficit=17 ∨ deficit=18 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|h <;> subst deficit
  · exact ⟨_,Scattered.supplied_extreme_graft 10 9 9 (by decide) (by decide) prefix9 _ prefix9_valid FullFixed.c10r9_odd⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 10 9 10 (by decide) (by decide) prefix9 _ prefix9_valid FullFixed.c10r9_even⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 10 9 11 (by decide) (by decide) prefix9 _ prefix9_valid FullFixed26.low9_c11⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 10 9 12 (by decide) (by decide) prefix9 _ prefix9_valid FullFixed26.low9_c12⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 8 11 13 (by decide) (by decide) prefix11 _ prefix11_valid Scattered.q11_high13⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 8 11 14 (by decide) (by decide) prefix11 _ prefix11_valid Scattered.q11_low14⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 7 12 15 (by decide) (by decide) prefix12 _ prefix12_valid Scattered.q12_high15⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 7 12 16 (by decide) (by decide) prefix12 _ prefix12_valid Scattered.q12_low16⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 4 15 17 (by decide) (by decide) prefix15 _ prefix15_valid FullFixed30.direct15_high⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 4 15 18 (by decide) (by decide) prefix15 _ prefix15_valid FullFixed30.direct15_low⟩

theorem tip34_core : FullFixed.RootZeroTip.CorePacket 17 (Scattered.tipList 17) := by constructor <;> decide
theorem tip34_zero (N : Nat) : (decode N false (Scattered.tipList 17))[34]?=some 0 := by rfl
theorem k34_tip_zero (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 34 → Nat, Graceful (spiderGraph n m 34) (n*34+m) f ∧ f (.arm a ⟨33,by decide⟩)=0 :=
  FullFixed.supplied_tip_zero 17 n m (by decide) (by omega) (Scattered.tipList 17) tip34_core tip34_zero a

end GracefulBoundary.FullFixed34
