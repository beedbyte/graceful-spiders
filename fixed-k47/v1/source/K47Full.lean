import K47Tip
import Q24MixFamily
import Q30Family
import K47Depth45
namespace GracefulBoundary.K47Full

theorem arm_depth_zero (n m : Nat) (hn : 2≤n) (a : Fin n) (d : Fin 47) :
    ∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (47*n+m) f ∧ f (.arm a d)=0 := by
  have bound := d.isLt
  by_cases old : d.val≤37
  · exact K47OldPackets.old_depth_zero n m hn a d old
  by_cases mix : d.val≤41
  · obtain ⟨_,f,hf,hz⟩ := Q24Mix.interval_actual 1 n m (d.val+1) hn a ⟨by omega,by omega⟩
    have he : (⟨d.val+1-1,by omega⟩ : Fin 47)=d := Fin.ext (by simp only [Nat.add_sub_cancel])
    refine ⟨f,?_,?_⟩
    · simpa only [Nat.mul_comm] using hf
    · simpa only [he] using hz
  by_cases q30 : d.val≤43
  · have split : d.val=42 ∨ d.val=43 := by omega
    rcases split with h|h
    · have he : d=⟨42,by decide⟩ := Fin.ext h
      rw [he]
      simpa only [Nat.mul_comm] using (Q30.actual 1 n m hn a).2
    · have he : d=⟨43,by decide⟩ := Fin.ext h
      rw [he]
      simpa only [Nat.mul_comm] using (Q30.actual 1 n m hn a).1
  by_cases direct : d.val=44
  · have he : d=⟨44,by decide⟩ := Fin.ext direct
    rw [he]
    exact K47Depth45.depth45_zero n m hn a
  · have split : d.val=45 ∨ d.val=46 := by omega
    rcases split with h|h
    · have he : d=⟨45,by decide⟩ := Fin.ext h
      rw [he]
      simpa only [Nat.mul_comm] using (K47Tip.tips_prescribed_zero n m (by omega) a).2
    · have he : d=⟨46,by decide⟩ := Fin.ext h
      rw [he]
      simpa only [Nat.mul_comm] using (K47Tip.tips_prescribed_zero n m (by omega) a).1

theorem all_vertices (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 47) :
    ∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (47*n+m) f ∧ f v=0 := by
  cases v with
  | center => exact K47Leaf.center_zero n m
  | leaf a => exact K47Leaf.leaf_zero n m a
  | arm a d => exact arm_depth_zero n m hn a d

theorem all_vertices_unique_zero (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 47) :
    ∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (47*n+m) f ∧ f v=0 ∧ (∀ w, f w=0 ↔ w=v) := by
  obtain ⟨f,hf,hv⟩ := all_vertices n m hn v
  refine ⟨f,hf,hv,?_⟩
  intro w
  constructor
  · intro hw
    exact hf.vertices.injective w v (by rw [hw,hv])
  · intro hw
    rw [hw]; exact hv

end GracefulBoundary.K47Full
