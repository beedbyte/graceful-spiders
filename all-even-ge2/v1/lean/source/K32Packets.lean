import K32Certificates
namespace GracefulBoundary.FullFixed32
open EvenBoundary.Flexible

def prefix9 : List Nat := [17,14,14,15,15,12,12,13,13,10,11,11,9,9,10]
def prefix11 : List Nat := [17,14,14,15,15,12,13,13,11,11,12]
def prefix12 : List Nat := [17,14,14,15,15,12,12,13,13]
theorem prefix9_valid : TailGraft.RetainedPrefix 9 9 prefix9 := by constructor <;> decide
theorem prefix11_valid : TailGraft.RetainedPrefix 7 11 prefix11 := by constructor <;> decide
theorem prefix12_valid : TailGraft.RetainedPrefix 6 12 prefix12 := by constructor <;> decide

theorem k32_packet_band (deficit : Nat) (hd : 9≤deficit ∧ deficit≤16) : ∃c,ExtremePacket 16 deficit c := by
  have cases : deficit=9 ∨ deficit=10 ∨ deficit=11 ∨ deficit=12 ∨ deficit=13 ∨ deficit=14 ∨ deficit=15 ∨ deficit=16 := by omega
  rcases cases with h|h|h|h|h|h|h|h <;> subst deficit
  · exact ⟨_,Scattered.supplied_extreme_graft 9 9 9 (by decide) (by decide) prefix9 _ prefix9_valid FullFixed.c10r9_odd⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 9 9 10 (by decide) (by decide) prefix9 _ prefix9_valid FullFixed.c10r9_even⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 9 9 11 (by decide) (by decide) prefix9 _ prefix9_valid FullFixed26.low9_c11⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 9 9 12 (by decide) (by decide) prefix9 _ prefix9_valid FullFixed26.low9_c12⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 7 11 13 (by decide) (by decide) prefix11 _ prefix11_valid Scattered.q11_high13⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 7 11 14 (by decide) (by decide) prefix11 _ prefix11_valid Scattered.q11_low14⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 6 12 15 (by decide) (by decide) prefix12 _ prefix12_valid Scattered.q12_high15⟩
  · exact ⟨_,Scattered.supplied_extreme_graft 6 12 16 (by decide) (by decide) prefix12 _ prefix12_valid Scattered.q12_low16⟩

theorem tip32_core : FullFixed.RootZeroTip.CorePacket 16 (Scattered.tipList 16) := by constructor <;> decide
theorem tip32_zero (N : Nat) : (decode N false (Scattered.tipList 16))[32]?=some 0 := by rfl
theorem k32_tip_zero (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 32 → Nat, Graceful (spiderGraph n m 32) (n*32+m) f ∧ f (.arm a ⟨31,by decide⟩)=0 :=
  FullFixed.supplied_tip_zero 16 n m (by decide) (by omega) (Scattered.tipList 16) tip32_core tip32_zero a

end GracefulBoundary.FullFixed32
