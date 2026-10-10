import ShellPromotion
namespace GracefulBoundary.LowBand
open EvenBoundary EvenBoundary.Flexible

theorem packets_9_22 (R deficit : Nat) (hR : 23≤R) (hd : 9≤deficit ∧ deficit≤22) :
    ∃c,ExtremePacket R deficit c := by
  have cases : deficit=9 ∨ deficit=10 ∨ deficit=11 ∨ deficit=12 ∨ deficit=13 ∨ deficit=14 ∨ deficit=15 ∨ deficit=16 ∨ deficit=17 ∨ deficit=18 ∨ deficit=19 ∨ deficit=20 ∨ deficit=21 ∨ deficit=22 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst deficit
  · exact promote 9 R 9 (by decide) (by omega) _ FullFixed.c10r9_odd
  · exact promote 9 R 10 (by decide) (by omega) _ FullFixed.c10r9_even
  · exact promote 9 R 11 (by decide) (by omega) _ FullFixed26.low9_c11
  · exact promote 9 R 12 (by decide) (by omega) _ FullFixed26.low9_c12
  · exact promote 11 R 13 (by decide) (by omega) _ Scattered.q11_high13
  · exact promote 11 R 14 (by decide) (by omega) _ Scattered.q11_low14
  · exact promote 12 R 15 (by decide) (by omega) _ Scattered.q12_high15
  · exact promote 12 R 16 (by decide) (by omega) _ Scattered.q12_low16
  · exact promote 15 R 17 (by decide) (by omega) _ Deficit24.q15_c17
  · exact promote 15 R 18 (by decide) (by omega) _ Deficit24.q15_c18
  · exact promote 17 R 19 (by decide) (by omega) _ Deficit24.q17_c19
  · exact promote 17 R 20 (by decide) (by omega) _ Deficit24.q17_c20
  · exact promote 21 R 21 (by decide) (by omega) _ Deficit24.q21late_c21
  · exact promote 21 R 22 (by decide) (by omega) _ Deficit24.q21late_c22

theorem packets_1_22 (R deficit : Nat) (hR : 23≤R) (hd : 1≤deficit ∧ deficit≤22) :
    ∃c,ExtremePacket R deficit c := by
  by_cases small : deficit≤8
  · exact all_eight_extreme_packets R deficit (by omega) ⟨hd.1,small⟩
  · exact packets_9_22 R deficit hR ⟨by omega,hd.2⟩

theorem bridge_membership (R : Nat) (hR : 18≤R ∧ R≤22) : 2*R∈Scattered.lengths := by
  rw [Scattered.exact_length_membership]
  omega

/-- Low deficits 1..22 for k≥46, and every interior depth for the five bridges. -/
theorem named_low_deficit (R n m d : Nat) (hR : 18≤R) (hn : 2≤n)
    (a : Fin n) (hd : 2≤d) (hlt : d<2*R) (hband : 2*R-d≤22) :
    NamedDepthZero R n m d a := by
  by_cases bridge : R≤22
  · have hit : d-1<2*R := by omega
    obtain ⟨f,hf,hzero⟩ := Scattered.scattered_full_zero_rotatability (2*R) n m
      (bridge_membership R ⟨hR,bridge⟩) hn (.arm a ⟨d-1,hit⟩)
    exact ⟨hit,f,hf,hzero⟩
  · obtain ⟨c,hc⟩ := packets_1_22 R (2*R-d) (by omega) ⟨by omega,hband⟩
    obtain ⟨hit,f,hf,hzero⟩ := named_arm_zero_from_packet R n m (2*R-d) (by omega) hn a c hc
    have depth : 2*R-(2*R-d)-1=d-1 := by omega
    exact ⟨by omega,f,hf,by simpa only [depth] using hzero⟩

end GracefulBoundary.LowBand
