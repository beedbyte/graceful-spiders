import FixedDepthSeeds
import EvenTransfer
import EightDepthTheorem
import CenterBoundary
import UniversalTip

namespace GracefulBoundary.K16Existing

theorem depth_2_7 (n m d : Nat) (hn : 2 ≤ n)
    (hd : 2 ≤ d ∧ d ≤ 7) (a : Fin n) :
    ∃ (hlt : d-1 < 16) (f : SpiderVertex n m 16 → Nat),
      Graceful (spiderGraph n m 16) (n*16+m) f ∧
      f (.arm a ⟨d-1,hlt⟩) = 0 := by
  obtain ⟨z,q,c,hc,hv⟩ :
      ∃ z q c, FixedDepth.CorePair 6 z q c ∧ (d=z ∨ d=q) := by
    have cases : d=2 ∨ d=3 ∨ d=4 ∨ d=5 ∨ d=6 ∨ d=7 := by omega
    rcases cases with h|h|h|h|h|h
    · exact ⟨2,3,FixedDepth.B6_2,FixedDepth.B6_2_valid,by omega⟩
    · exact ⟨2,3,FixedDepth.B6_2,FixedDepth.B6_2_valid,by omega⟩
    · exact ⟨4,5,FixedDepth.B6_4,FixedDepth.B6_4_valid,by omega⟩
    · exact ⟨4,5,FixedDepth.B6_4,FixedDepth.B6_4_valid,by omega⟩
    · exact ⟨6,7,FixedDepth.B6_6,FixedDepth.B6_6_valid,by omega⟩
    · exact ⟨6,7,FixedDepth.B6_6,FixedDepth.B6_6_valid,by omega⟩
  have hp := Even.core_pair_spider_transfer 6 z q n m c hc hn a
  rcases hv with hv|hv
  · subst d
    obtain ⟨f,hf,hz⟩ := hp.1
    exact ⟨by omega,f,hf,by simpa using hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := hp.2
    exact ⟨by omega,f,hf,by simpa using hz⟩

theorem full_actual (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 16) :
    ∃ f : SpiderVertex n m 16 → Nat,
      Graceful (spiderGraph n m 16) (n*16+m) f ∧ f v = 0 := by
  cases v with
  | center => exact FullFixed.center_zero 8 n m (by decide)
  | leaf a => exact FullFixed.short_leaf_zero 8 n m (by decide) a
  | arm a ix =>
    by_cases first : ix.val = 0
    · have eq : ix = ⟨0,by decide⟩ := Fin.ext first
      rw [eq]
      exact FullFixed.depth_one_zero 8 n m (by decide) hn a
    by_cases last : ix.val = 15
    · have eq : ix = ⟨15,by decide⟩ := Fin.ext last
      rw [eq]
      exact LowBand.actual_tip_zero 8 n m (by decide) (by omega) a
    by_cases shallow : ix.val+1 ≤ 7
    · obtain ⟨hlt,f,hf,hz⟩ := depth_2_7 n m (ix.val+1) hn ⟨by omega,shallow⟩ a
      have eq : (⟨ix.val+1-1,hlt⟩ : Fin 16) = ix := Fin.ext (by dsimp only; omega)
      exact ⟨f,hf,by simpa only [eq] using hz⟩
    · obtain ⟨hlt,f,hf,hz⟩ := EvenBoundary.all_even_eight_depths_n_ge_two
        16 n m (ix.val+1) (by decide) (by decide) hn ⟨by omega,by omega⟩ a
      have eq : (⟨ix.val+1-1,hlt⟩ : Fin 16) = ix := Fin.ext (by dsimp only; omega)
      exact ⟨f,hf,by simpa only [eq] using hz⟩

theorem n2_m0_all_vertices (v : SpiderVertex 2 0 16) :
    ∃ f : SpiderVertex 2 0 16 → Nat,
      Graceful (spiderGraph 2 0 16) 32 f ∧ f v = 0 :=
  full_actual 2 0 (by decide) v

theorem n2_m1_all_vertices (v : SpiderVertex 2 1 16) :
    ∃ f : SpiderVertex 2 1 16 → Nat,
      Graceful (spiderGraph 2 1 16) 33 f ∧ f v = 0 :=
  full_actual 2 1 (by decide) v

theorem full_unique_zero (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 16) :
    ∃ f : SpiderVertex n m 16 → Nat,
      Graceful (spiderGraph n m 16) (n*16+m) f ∧
      f v = 0 ∧ ∀ w, w ≠ v → 0 < f w := by
  obtain ⟨f,hf,hz⟩ := full_actual n m hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have nonzero : f w ≠ 0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega
end GracefulBoundary.K16Existing

#print axioms GracefulBoundary.K16Existing.depth_2_7
#print axioms GracefulBoundary.K16Existing.full_actual
#print axioms GracefulBoundary.K16Existing.n2_m0_all_vertices
#print axioms GracefulBoundary.K16Existing.n2_m1_all_vertices
#print axioms GracefulBoundary.K16Existing.full_unique_zero
