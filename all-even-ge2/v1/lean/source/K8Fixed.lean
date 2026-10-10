import EvenTransfer
import GenericShellTransfer
import CenterBoundary
import UniversalTip

namespace GracefulBoundary.K8Fixed

def path2 : List Nat := [3,15,2,12,1,16,0,14,8,9,7,10,6,11,4,13,5]
def path4 : List Nat := [5,15,1,16,0,13,4,11,8,9,7,12,6,10,2,14,3]
def path6 : List Nat := [3,16,0,15,1,13,2,11,8,9,7,14,4,12,6,10,5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem path2_certificate : Even.Certificate 2 2 3 path2 := by
  unfold Even.Certificate Even.GenericPathCertificate path2
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem path4_certificate : Even.Certificate 2 4 5 path4 := by
  unfold Even.Certificate Even.GenericPathCertificate path4
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem path6_certificate : Even.Certificate 2 6 7 path6 := by
  unfold Even.Certificate Even.GenericPathCertificate path6
  decide

/-- Old radius-four source; optional overlapping evidence, not a k>=16 premise. -/
def shellB : List Nat := [5,2,2,3,3,0,0,1,1]
theorem shellB_c2 : EvenBoundary.Flexible.ExtremePacket 4 2 shellB := by
  constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem shellB_c3 : EvenBoundary.Flexible.ExtremePacket 4 3 shellB := by
  constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)

theorem old_shell_depth_5_6 (n m d : Nat) (hn : 2 <= n)
    (hd : 5 <= d ∧ d <= 6) (a : Fin n) :
    ∃ (hlt : d-1 < 8) (f : SpiderVertex n m 8 → Nat),
      Graceful (spiderGraph n m 8) (n*8+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  have cases : d=5 ∨ d=6 := by omega
  rcases cases with h|h <;> subst d
  · exact EvenBoundary.named_arm_zero_from_packet 4 n m 3 (by decide) hn a shellB shellB_c3
  · exact EvenBoundary.named_arm_zero_from_packet 4 n m 2 (by decide) hn a shellB shellB_c2

theorem internal_zero (n m d : Nat) (hn : 2 <= n)
    (hd : 2 <= d ∧ d <= 7) (a : Fin n) :
    ∃ (hlt : d-1 < 8) (f : SpiderVertex n m 8 → Nat),
      Graceful (spiderGraph n m 8) (n*8+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  have cases : d=2 ∨ d=3 ∨ d=4 ∨ d=5 ∨ d=6 ∨ d=7 := by omega
  have hp2 := Even.prescribed_zero 2 2 3 n m path2 path2_certificate hn a
  have hp4 := Even.prescribed_zero 2 4 5 n m path4 path4_certificate hn a
  have hp6 := Even.prescribed_zero 2 6 7 n m path6 path6_certificate hn a
  rcases cases with h|h|h|h|h|h <;> subst d
  · obtain ⟨f,hf,hz⟩ := hp2.1; exact ⟨by decide,f,hf,by simpa using hz⟩
  · obtain ⟨f,hf,hz⟩ := hp2.2; exact ⟨by decide,f,hf,by simpa using hz⟩
  · obtain ⟨f,hf,hz⟩ := hp4.1; exact ⟨by decide,f,hf,by simpa using hz⟩
  · obtain ⟨f,hf,hz⟩ := hp4.2; exact ⟨by decide,f,hf,by simpa using hz⟩
  · obtain ⟨f,hf,hz⟩ := hp6.1; exact ⟨by decide,f,hf,by simpa using hz⟩
  · obtain ⟨f,hf,hz⟩ := hp6.2; exact ⟨by decide,f,hf,by simpa using hz⟩

/-- Fixed length eight only. Each actual named target may use a different labeling. -/
theorem full_actual (n m : Nat) (hn : 2 <= n) (v : SpiderVertex n m 8) :
    ∃ f : SpiderVertex n m 8 → Nat,
      Graceful (spiderGraph n m 8) (n*8+m) f ∧ f v=0 := by
  cases v with
  | center => exact FullFixed.center_zero 4 n m (by decide)
  | leaf a => exact FullFixed.short_leaf_zero 4 n m (by decide) a
  | arm a ix =>
    by_cases first : ix.val=0
    · have eq : ix=⟨0,by decide⟩ := Fin.ext first
      rw [eq]
      exact FullFixed.depth_one_zero 4 n m (by decide) hn a
    by_cases last : ix.val=7
    · have eq : ix=⟨7,by decide⟩ := Fin.ext last
      rw [eq]
      exact LowBand.actual_tip_zero 4 n m (by decide) (by omega) a
    obtain ⟨hlt,f,hf,hz⟩ := internal_zero n m (ix.val+1) hn ⟨by omega,by omega⟩ a
    have eq : (⟨ix.val+1-1,hlt⟩ : Fin 8)=ix := Fin.ext (by dsimp only; omega)
    exact ⟨f,hf,by simpa only [eq] using hz⟩

theorem n2_m0_all_vertices (v : SpiderVertex 2 0 8) :
    ∃ f : SpiderVertex 2 0 8 → Nat,
      Graceful (spiderGraph 2 0 8) 16 f ∧ f v=0 := full_actual 2 0 (by decide) v
theorem n2_m1_all_vertices (v : SpiderVertex 2 1 8) :
    ∃ f : SpiderVertex 2 1 8 → Nat,
      Graceful (spiderGraph 2 1 8) 17 f ∧ f v=0 := full_actual 2 1 (by decide) v

theorem endpoint_zero (n m : Nat) (hn : 2 <= n) (a : Fin n) :
    ∃ f : SpiderVertex n m 8 → Nat,
      Graceful (spiderGraph n m 8) (n*8+m) f ∧ f (.arm a ⟨7,by decide⟩)=0 :=
  LowBand.actual_tip_zero 4 n m (by decide) (by omega) a

theorem full_unique_zero (n m : Nat) (hn : 2 <= n) (v : SpiderVertex n m 8) :
    ∃ f : SpiderVertex n m 8 → Nat,
      Graceful (spiderGraph n m 8) (n*8+m) f ∧ f v=0 ∧ ∀ w, w≠v → 0<f w := by
  obtain ⟨f,hf,hz⟩ := full_actual n m hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have nonzero : f w≠0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.K8Fixed

#print axioms GracefulBoundary.K8Fixed.path2_certificate
#print axioms GracefulBoundary.K8Fixed.path4_certificate
#print axioms GracefulBoundary.K8Fixed.path6_certificate
#print axioms GracefulBoundary.K8Fixed.shellB_c2
#print axioms GracefulBoundary.K8Fixed.shellB_c3
#print axioms GracefulBoundary.K8Fixed.old_shell_depth_5_6
#print axioms GracefulBoundary.K8Fixed.internal_zero
#print axioms GracefulBoundary.K8Fixed.full_actual
#print axioms GracefulBoundary.K8Fixed.n2_m0_all_vertices
#print axioms GracefulBoundary.K8Fixed.n2_m1_all_vertices
#print axioms GracefulBoundary.K8Fixed.endpoint_zero
#print axioms GracefulBoundary.K8Fixed.full_unique_zero
