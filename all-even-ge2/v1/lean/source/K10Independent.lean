import EvenTransfer
import GenericShellTransfer
import CenterBoundary
import UniversalTip

namespace GracefulBoundary.K10Independent

def path21 : List Nat :=
  [7,15,5,14,2,19,1,20,0,16,10,
   11,9,12,8,13,6,17,4,18,3]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem path21_certificate : Even.Certificate 3 2 3 path21 := by
  unfold Even.Certificate Even.GenericPathCertificate path21
  decide

theorem radius5_packets (deficit : Nat) (hd : 1 ≤ deficit ∧ deficit ≤ 7) :
    ∃ c, EvenBoundary.Flexible.ExtremePacket 5 deficit c := by
  have cases : deficit=1 ∨ deficit=2 ∨ deficit=3 ∨ deficit=4 ∨
      deficit=5 ∨ deficit=6 ∨ deficit=7 := by omega
  rcases cases with h|h|h|h|h|h|h <;> subst deficit
  · exact ⟨_,EvenBoundary.Flexible.s52_c1⟩
  · exact ⟨_,EvenBoundary.Flexible.s52_c2⟩
  · exact ⟨_,EvenBoundary.Flexible.s54_c3⟩
  · exact ⟨_,EvenBoundary.Flexible.s54_c4⟩
  · exact ⟨_,EvenBoundary.Flexible.s54alt_c5⟩
  · exact ⟨_,EvenBoundary.Flexible.s56_c6⟩
  · exact ⟨_,EvenBoundary.Flexible.s56_c7⟩

theorem depth_2_3 (n m d : Nat) (hn : 2 ≤ n)
    (hd : 2 ≤ d ∧ d ≤ 3) (a : Fin n) :
    ∃ (hlt : d-1 < 10) (f : SpiderVertex n m 10 → Nat),
      Graceful (spiderGraph n m 10) (n*10+m) f ∧
      f (.arm a ⟨d-1,hlt⟩) = 0 := by
  have hp := Even.prescribed_zero 3 2 3 n m path21 path21_certificate hn a
  have cases : d=2 ∨ d=3 := by omega
  rcases cases with h|h
  · subst d
    obtain ⟨f,hf,hz⟩ := hp.1
    exact ⟨by decide,f,hf,by simpa using hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := hp.2
    exact ⟨by decide,f,hf,by simpa using hz⟩

theorem depth_4_9 (n m d : Nat) (hn : 2 ≤ n)
    (hd : 4 ≤ d ∧ d ≤ 9) (a : Fin n) :
    ∃ (hlt : d-1 < 10) (f : SpiderVertex n m 10 → Nat),
      Graceful (spiderGraph n m 10) (n*10+m) f ∧
      f (.arm a ⟨d-1,hlt⟩) = 0 := by
  obtain ⟨c,hc⟩ := radius5_packets (10-d) (by omega)
  obtain ⟨hlt,f,hf,hz⟩ := EvenBoundary.named_arm_zero_from_packet
    5 n m (10-d) (by decide) hn a c hc
  have idx : 2*5-(10-d)-1=d-1 := by omega
  exact ⟨by omega,f,hf,by simpa only [idx] using hz⟩

theorem full_actual (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 10) :
    ∃ f : SpiderVertex n m 10 → Nat,
      Graceful (spiderGraph n m 10) (n*10+m) f ∧ f v = 0 := by
  cases v with
  | center => exact FullFixed.center_zero 5 n m (by decide)
  | leaf a => exact FullFixed.short_leaf_zero 5 n m (by decide) a
  | arm a ix =>
    by_cases first : ix.val = 0
    · have eq : ix = ⟨0,by decide⟩ := Fin.ext first
      rw [eq]
      exact FullFixed.depth_one_zero 5 n m (by decide) hn a
    by_cases last : ix.val = 9
    · have eq : ix = ⟨9,by decide⟩ := Fin.ext last
      rw [eq]
      exact LowBand.actual_tip_zero 5 n m (by decide) (by omega) a
    by_cases early : ix.val+1 ≤ 3
    · obtain ⟨hlt,f,hf,hz⟩ := depth_2_3 n m (ix.val+1) hn ⟨by omega,early⟩ a
      have eq : (⟨ix.val+1-1,hlt⟩ : Fin 10)=ix := Fin.ext (by dsimp only; omega)
      exact ⟨f,hf,by simpa only [eq] using hz⟩
    · obtain ⟨hlt,f,hf,hz⟩ := depth_4_9 n m (ix.val+1) hn ⟨by omega,by omega⟩ a
      have eq : (⟨ix.val+1-1,hlt⟩ : Fin 10)=ix := Fin.ext (by dsimp only; omega)
      exact ⟨f,hf,by simpa only [eq] using hz⟩

theorem n2_m0_all_vertices (v : SpiderVertex 2 0 10) :
    ∃ f : SpiderVertex 2 0 10 → Nat,
      Graceful (spiderGraph 2 0 10) 20 f ∧ f v = 0 :=
  full_actual 2 0 (by decide) v

theorem n2_m1_all_vertices (v : SpiderVertex 2 1 10) :
    ∃ f : SpiderVertex 2 1 10 → Nat,
      Graceful (spiderGraph 2 1 10) 21 f ∧ f v = 0 :=
  full_actual 2 1 (by decide) v

theorem full_unique_zero (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 10) :
    ∃ f : SpiderVertex n m 10 → Nat,
      Graceful (spiderGraph n m 10) (n*10+m) f ∧
      f v=0 ∧ ∀ w, w≠v → 0<f w := by
  obtain ⟨f,hf,hz⟩ := full_actual n m hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have nonzero : f w≠0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.K10Independent

#print axioms GracefulBoundary.K10Independent.path21_certificate
#print axioms GracefulBoundary.K10Independent.radius5_packets
#print axioms GracefulBoundary.K10Independent.depth_2_3
#print axioms GracefulBoundary.K10Independent.depth_4_9
#print axioms GracefulBoundary.K10Independent.full_actual
#print axioms GracefulBoundary.K10Independent.n2_m0_all_vertices
#print axioms GracefulBoundary.K10Independent.n2_m1_all_vertices
#print axioms GracefulBoundary.K10Independent.full_unique_zero
