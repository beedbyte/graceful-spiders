import EvenTransfer
import GenericShellTransfer
import CenterBoundary
import UniversalTip

namespace GracefulBoundary.K12Independent

def path25 : List Nat :=
  [7,17,9,16,3,22,2,23,1,24,0,18,12,
   13,11,14,10,15,6,20,8,19,4,21,5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem path25_certificate : Even.Certificate 4 2 3 path25 := by
  unfold Even.Certificate Even.GenericPathCertificate path25
  decide

theorem radius6_packets (deficit : Nat) (hd : 1 ≤ deficit ∧ deficit ≤ 8) :
    ∃ c, EvenBoundary.Flexible.ExtremePacket 6 deficit c := by
  have cases : deficit=1 ∨ deficit=2 ∨ deficit=3 ∨ deficit=4 ∨
      deficit=5 ∨ deficit=6 ∨ deficit=7 ∨ deficit=8 := by omega
  rcases cases with h|h|h|h|h|h|h|h <;> subst deficit
  · exact ⟨_,EvenBoundary.Flexible.s62_c1⟩
  · exact ⟨_,EvenBoundary.Flexible.s62_c2⟩
  · exact ⟨_,EvenBoundary.Flexible.s64_c3⟩
  · exact ⟨_,EvenBoundary.Flexible.s64_c4⟩
  · exact ⟨_,EvenBoundary.Flexible.s66_c5⟩
  · exact ⟨_,EvenBoundary.Flexible.s66_c6⟩
  · exact ⟨_,EvenBoundary.Flexible.s68_c7⟩
  · exact ⟨_,EvenBoundary.Flexible.s68_c8⟩

theorem depth_2_3 (n m d : Nat) (hn : 2 ≤ n)
    (hd : 2 ≤ d ∧ d ≤ 3) (a : Fin n) :
    ∃ (hlt : d-1 < 12) (f : SpiderVertex n m 12 → Nat),
      Graceful (spiderGraph n m 12) (n*12+m) f ∧
      f (.arm a ⟨d-1,hlt⟩) = 0 := by
  have hp := Even.prescribed_zero 4 2 3 n m path25 path25_certificate hn a
  have cases : d=2 ∨ d=3 := by omega
  rcases cases with h|h
  · subst d
    obtain ⟨f,hf,hz⟩ := hp.1
    exact ⟨by decide,f,hf,by simpa using hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := hp.2
    exact ⟨by decide,f,hf,by simpa using hz⟩

theorem depth_4_11 (n m d : Nat) (hn : 2 ≤ n)
    (hd : 4 ≤ d ∧ d ≤ 11) (a : Fin n) :
    ∃ (hlt : d-1 < 12) (f : SpiderVertex n m 12 → Nat),
      Graceful (spiderGraph n m 12) (n*12+m) f ∧
      f (.arm a ⟨d-1,hlt⟩) = 0 := by
  obtain ⟨c,hc⟩ := radius6_packets (12-d) (by omega)
  obtain ⟨hlt,f,hf,hz⟩ := EvenBoundary.named_arm_zero_from_packet
    6 n m (12-d) (by decide) hn a c hc
  have idx : 2*6-(12-d)-1=d-1 := by omega
  exact ⟨by omega,f,hf,by simpa only [idx] using hz⟩

theorem full_actual (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 12) :
    ∃ f : SpiderVertex n m 12 → Nat,
      Graceful (spiderGraph n m 12) (n*12+m) f ∧ f v = 0 := by
  cases v with
  | center => exact FullFixed.center_zero 6 n m (by decide)
  | leaf a => exact FullFixed.short_leaf_zero 6 n m (by decide) a
  | arm a ix =>
    by_cases first : ix.val = 0
    · have eq : ix = ⟨0,by decide⟩ := Fin.ext first
      rw [eq]
      exact FullFixed.depth_one_zero 6 n m (by decide) hn a
    by_cases last : ix.val = 11
    · have eq : ix = ⟨11,by decide⟩ := Fin.ext last
      rw [eq]
      exact LowBand.actual_tip_zero 6 n m (by decide) (by omega) a
    by_cases early : ix.val+1 ≤ 3
    · obtain ⟨hlt,f,hf,hz⟩ := depth_2_3 n m (ix.val+1) hn ⟨by omega,early⟩ a
      have eq : (⟨ix.val+1-1,hlt⟩ : Fin 12)=ix := Fin.ext (by dsimp only; omega)
      exact ⟨f,hf,by simpa only [eq] using hz⟩
    · obtain ⟨hlt,f,hf,hz⟩ := depth_4_11 n m (ix.val+1) hn ⟨by omega,by omega⟩ a
      have eq : (⟨ix.val+1-1,hlt⟩ : Fin 12)=ix := Fin.ext (by dsimp only; omega)
      exact ⟨f,hf,by simpa only [eq] using hz⟩

theorem n2_m0_all_vertices (v : SpiderVertex 2 0 12) :
    ∃ f : SpiderVertex 2 0 12 → Nat,
      Graceful (spiderGraph 2 0 12) 24 f ∧ f v = 0 :=
  full_actual 2 0 (by decide) v

theorem n2_m1_all_vertices (v : SpiderVertex 2 1 12) :
    ∃ f : SpiderVertex 2 1 12 → Nat,
      Graceful (spiderGraph 2 1 12) 25 f ∧ f v = 0 :=
  full_actual 2 1 (by decide) v

theorem full_unique_zero (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 12) :
    ∃ f : SpiderVertex n m 12 → Nat,
      Graceful (spiderGraph n m 12) (n*12+m) f ∧
      f v=0 ∧ ∀ w, w≠v → 0<f w := by
  obtain ⟨f,hf,hz⟩ := full_actual n m hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have nonzero : f w≠0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.K12Independent

#print axioms GracefulBoundary.K12Independent.path25_certificate
#print axioms GracefulBoundary.K12Independent.radius6_packets
#print axioms GracefulBoundary.K12Independent.depth_2_3
#print axioms GracefulBoundary.K12Independent.depth_4_11
#print axioms GracefulBoundary.K12Independent.full_actual
#print axioms GracefulBoundary.K12Independent.n2_m0_all_vertices
#print axioms GracefulBoundary.K12Independent.n2_m1_all_vertices
#print axioms GracefulBoundary.K12Independent.full_unique_zero
