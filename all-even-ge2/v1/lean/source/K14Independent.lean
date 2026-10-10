import EvenTransfer
import FixedDepthSeeds
import GenericShellTransfer
import CenterBoundary
import UniversalTip

namespace GracefulBoundary.K14Independent

def path29 : List Nat :=
  [8,23,7,20,9,21,4,22,2,27,1,28,0,24,14,
   15,13,16,12,17,11,18,10,19,5,26,3,25,6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem path29_certificate : Even.Certificate 5 2 3 path29 := by
  unfold Even.Certificate Even.GenericPathCertificate path29
  decide

def core34 : List Nat := [3,2,0,0,1,3,4,4,2,1]
def core56 : List Nat := [3,4,4,2,0,0,1,3,2,1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem core34_valid : FixedDepth.CorePair 5 4 3 core34 := by
  constructor
  · unfold BoundaryCore core34
    decide
  all_goals decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem core56_valid : FixedDepth.CorePair 5 6 5 core56 := by
  constructor
  · unfold BoundaryCore core56
    decide
  all_goals decide

theorem radius7_packets (deficit : Nat) (hd : 1 ≤ deficit ∧ deficit ≤ 7) :
    ∃ c, EvenBoundary.Flexible.ExtremePacket 7 deficit c := by
  have cases : deficit=1 ∨ deficit=2 ∨ deficit=3 ∨ deficit=4 ∨
      deficit=5 ∨ deficit=6 ∨ deficit=7 := by omega
  rcases cases with h|h|h|h|h|h|h <;> subst deficit
  · exact ⟨_,EvenBoundary.Flexible.extreme_packet_step 5 1 _
      EvenBoundary.Flexible.s52_c1⟩
  · exact ⟨_,EvenBoundary.Flexible.extreme_packet_step 5 2 _
      EvenBoundary.Flexible.s52_c2⟩
  · exact ⟨_,EvenBoundary.Flexible.extreme_packet_step 5 3 _
      EvenBoundary.Flexible.s54_c3⟩
  · exact ⟨_,EvenBoundary.Flexible.extreme_packet_step 5 4 _
      EvenBoundary.Flexible.s54_c4⟩
  · exact ⟨_,EvenBoundary.Flexible.extreme_packet_step 5 5 _
      EvenBoundary.Flexible.s54alt_c5⟩
  · exact ⟨_,EvenBoundary.Flexible.extreme_packet_step 5 6 _
      EvenBoundary.Flexible.s56_c6⟩
  · exact ⟨_,EvenBoundary.Flexible.extreme_packet_step 5 7 _
      EvenBoundary.Flexible.s56_c7⟩

theorem depth_2_3 (n m d : Nat) (hn : 2 ≤ n)
    (hd : 2 ≤ d ∧ d ≤ 3) (a : Fin n) :
    ∃ (hlt : d-1 < 14) (f : SpiderVertex n m 14 → Nat),
      Graceful (spiderGraph n m 14) (n*14+m) f ∧
      f (.arm a ⟨d-1,hlt⟩) = 0 := by
  have hp := Even.prescribed_zero 5 2 3 n m path29 path29_certificate hn a
  have cases : d=2 ∨ d=3 := by omega
  rcases cases with h|h
  · subst d
    obtain ⟨f,hf,hz⟩ := hp.1
    exact ⟨by decide,f,hf,by simpa using hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := hp.2
    exact ⟨by decide,f,hf,by simpa using hz⟩

theorem depth_4_6 (n m d : Nat) (hn : 2 ≤ n)
    (hd : 4 ≤ d ∧ d ≤ 6) (a : Fin n) :
    ∃ (hlt : d-1 < 14) (f : SpiderVertex n m 14 → Nat),
      Graceful (spiderGraph n m 14) (n*14+m) f ∧
      f (.arm a ⟨d-1,hlt⟩) = 0 := by
  have cases : d=4 ∨ d=5 ∨ d=6 := by omega
  rcases cases with h|h|h
  · subst d
    obtain ⟨f,hf,hz⟩ :=
      (Even.core_pair_spider_transfer 5 4 3 n m core34 core34_valid hn a).1
    exact ⟨by decide,f,hf,by simpa using hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ :=
      (Even.core_pair_spider_transfer 5 6 5 n m core56 core56_valid hn a).2
    exact ⟨by decide,f,hf,by simpa using hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ :=
      (Even.core_pair_spider_transfer 5 6 5 n m core56 core56_valid hn a).1
    exact ⟨by decide,f,hf,by simpa using hz⟩

theorem depth_7_13 (n m d : Nat) (hn : 2 ≤ n)
    (hd : 7 ≤ d ∧ d ≤ 13) (a : Fin n) :
    ∃ (hlt : d-1 < 14) (f : SpiderVertex n m 14 → Nat),
      Graceful (spiderGraph n m 14) (n*14+m) f ∧
      f (.arm a ⟨d-1,hlt⟩) = 0 := by
  obtain ⟨c,hc⟩ := radius7_packets (14-d) (by omega)
  obtain ⟨hlt,f,hf,hz⟩ := EvenBoundary.named_arm_zero_from_packet
    7 n m (14-d) (by decide) hn a c hc
  have idx : 2*7-(14-d)-1=d-1 := by omega
  exact ⟨by omega,f,hf,by simpa only [idx] using hz⟩

theorem full_actual (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 14) :
    ∃ f : SpiderVertex n m 14 → Nat,
      Graceful (spiderGraph n m 14) (n*14+m) f ∧ f v = 0 := by
  cases v with
  | center => exact FullFixed.center_zero 7 n m (by decide)
  | leaf a => exact FullFixed.short_leaf_zero 7 n m (by decide) a
  | arm a ix =>
    by_cases first : ix.val = 0
    · have eq : ix = ⟨0,by decide⟩ := Fin.ext first
      rw [eq]
      exact FullFixed.depth_one_zero 7 n m (by decide) hn a
    by_cases last : ix.val = 13
    · have eq : ix = ⟨13,by decide⟩ := Fin.ext last
      rw [eq]
      exact LowBand.actual_tip_zero 7 n m (by decide) (by omega) a
    by_cases early : ix.val+1 ≤ 3
    · obtain ⟨hlt,f,hf,hz⟩ := depth_2_3 n m (ix.val+1) hn ⟨by omega,early⟩ a
      have eq : (⟨ix.val+1-1,hlt⟩ : Fin 14)=ix := Fin.ext (by dsimp only; omega)
      exact ⟨f,hf,by simpa only [eq] using hz⟩
    by_cases middle : ix.val+1 ≤ 6
    · obtain ⟨hlt,f,hf,hz⟩ := depth_4_6 n m (ix.val+1) hn ⟨by omega,middle⟩ a
      have eq : (⟨ix.val+1-1,hlt⟩ : Fin 14)=ix := Fin.ext (by dsimp only; omega)
      exact ⟨f,hf,by simpa only [eq] using hz⟩
    · obtain ⟨hlt,f,hf,hz⟩ := depth_7_13 n m (ix.val+1) hn ⟨by omega,by omega⟩ a
      have eq : (⟨ix.val+1-1,hlt⟩ : Fin 14)=ix := Fin.ext (by dsimp only; omega)
      exact ⟨f,hf,by simpa only [eq] using hz⟩

theorem n2_m0_all_vertices (v : SpiderVertex 2 0 14) :
    ∃ f : SpiderVertex 2 0 14 → Nat,
      Graceful (spiderGraph 2 0 14) 28 f ∧ f v = 0 :=
  full_actual 2 0 (by decide) v

theorem n2_m1_all_vertices (v : SpiderVertex 2 1 14) :
    ∃ f : SpiderVertex 2 1 14 → Nat,
      Graceful (spiderGraph 2 1 14) 29 f ∧ f v = 0 :=
  full_actual 2 1 (by decide) v

theorem full_unique_zero (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 14) :
    ∃ f : SpiderVertex n m 14 → Nat,
      Graceful (spiderGraph n m 14) (n*14+m) f ∧
      f v=0 ∧ ∀ w, w≠v → 0<f w := by
  obtain ⟨f,hf,hz⟩ := full_actual n m hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have nonzero : f w≠0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.K14Independent

#print axioms GracefulBoundary.K14Independent.path29_certificate
#print axioms GracefulBoundary.K14Independent.core34_valid
#print axioms GracefulBoundary.K14Independent.core56_valid
#print axioms GracefulBoundary.K14Independent.radius7_packets
#print axioms GracefulBoundary.K14Independent.depth_2_3
#print axioms GracefulBoundary.K14Independent.depth_4_6
#print axioms GracefulBoundary.K14Independent.depth_7_13
#print axioms GracefulBoundary.K14Independent.full_actual
#print axioms GracefulBoundary.K14Independent.n2_m0_all_vertices
#print axioms GracefulBoundary.K14Independent.n2_m1_all_vertices
#print axioms GracefulBoundary.K14Independent.full_unique_zero
