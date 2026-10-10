import GenericShellTransfer
import CenterBoundary
import UniversalTip

namespace GracefulBoundary.K6Existing

open EvenBoundary.Flexible

/-- The old private H3 cap, used here at its exact radius-three boundary. -/
def H3 : List Nat := [4,1,0,0,2,2,1]
/-- The old radius-three near-tip A packet. -/
def A3 : List Nat := [4,1,2,2,0,0,1]

theorem H3_depth2 : ExtremePacket 3 4 H3 := by
  constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem H3_depth3 : ExtremePacket 3 3 H3 := by
  constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem A3_depth4 : ExtremePacket 3 2 A3 := by
  constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem A3_depth5 : ExtremePacket 3 1 A3 := by
  constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)

theorem depth_2_5 (n m d : Nat) (hn : 2 ≤ n)
    (hd : 2 ≤ d ∧ d ≤ 5) (a : Fin n) :
    ∃ (hlt : d-1 < 6) (f : SpiderVertex n m 6 → Nat),
      Graceful (spiderGraph n m 6) (n*6+m) f ∧
      f (.arm a ⟨d-1,hlt⟩) = 0 := by
  have cases : d=2 ∨ d=3 ∨ d=4 ∨ d=5 := by omega
  rcases cases with h|h|h|h
  · subst d
    simpa only [show 2*3=6 by decide,show 2*3-4-1=2-1 by decide]
      using EvenBoundary.named_arm_zero_from_packet 3 n m 4 (by decide) hn a H3 H3_depth2
  · subst d
    simpa only [show 2*3=6 by decide,show 2*3-3-1=3-1 by decide]
      using EvenBoundary.named_arm_zero_from_packet 3 n m 3 (by decide) hn a H3 H3_depth3
  · subst d
    simpa only [show 2*3=6 by decide,show 2*3-2-1=4-1 by decide]
      using EvenBoundary.named_arm_zero_from_packet 3 n m 2 (by decide) hn a A3 A3_depth4
  · subst d
    simpa only [show 2*3=6 by decide,show 2*3-1-1=5-1 by decide]
      using EvenBoundary.named_arm_zero_from_packet 3 n m 1 (by decide) hn a A3 A3_depth5

theorem full_actual (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 6) :
    ∃ f : SpiderVertex n m 6 → Nat,
      Graceful (spiderGraph n m 6) (n*6+m) f ∧ f v = 0 := by
  cases v with
  | center => exact FullFixed.center_zero 3 n m (by decide)
  | leaf a => exact FullFixed.short_leaf_zero 3 n m (by decide) a
  | arm a ix =>
    by_cases first : ix.val = 0
    · have eq : ix = ⟨0,by decide⟩ := Fin.ext first
      rw [eq]
      exact FullFixed.depth_one_zero 3 n m (by decide) hn a
    by_cases last : ix.val = 5
    · have eq : ix = ⟨5,by decide⟩ := Fin.ext last
      rw [eq]
      exact LowBand.actual_tip_zero 3 n m (by decide) (by omega) a
    · obtain ⟨hlt,f,hf,hz⟩ := depth_2_5 n m (ix.val+1) hn ⟨by omega,by omega⟩ a
      have eq : (⟨ix.val+1-1,hlt⟩ : Fin 6) = ix := Fin.ext (by dsimp only; omega)
      exact ⟨f,hf,by simpa only [eq] using hz⟩

theorem n2_m0_all_vertices (v : SpiderVertex 2 0 6) :
    ∃ f : SpiderVertex 2 0 6 → Nat,
      Graceful (spiderGraph 2 0 6) 12 f ∧ f v = 0 :=
  full_actual 2 0 (by decide) v

theorem n2_m1_all_vertices (v : SpiderVertex 2 1 6) :
    ∃ f : SpiderVertex 2 1 6 → Nat,
      Graceful (spiderGraph 2 1 6) 13 f ∧ f v = 0 :=
  full_actual 2 1 (by decide) v

theorem full_unique_zero (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 6) :
    ∃ f : SpiderVertex n m 6 → Nat,
      Graceful (spiderGraph n m 6) (n*6+m) f ∧
      f v = 0 ∧ ∀ w, w ≠ v → 0 < f w := by
  obtain ⟨f,hf,hz⟩ := full_actual n m hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have hnonzero : f w ≠ 0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.K6Existing

#print axioms GracefulBoundary.K6Existing.H3_depth2
#print axioms GracefulBoundary.K6Existing.H3_depth3
#print axioms GracefulBoundary.K6Existing.A3_depth4
#print axioms GracefulBoundary.K6Existing.A3_depth5
#print axioms GracefulBoundary.K6Existing.depth_2_5
#print axioms GracefulBoundary.K6Existing.full_actual
#print axioms GracefulBoundary.K6Existing.n2_m0_all_vertices
#print axioms GracefulBoundary.K6Existing.n2_m1_all_vertices
#print axioms GracefulBoundary.K6Existing.full_unique_zero
