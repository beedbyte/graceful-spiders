import K71CatalogActual
import Q24Seed5Mix
import K71Tip

namespace GracefulBoundary.K71Full

theorem arm_from_depth (n m : Nat) (a : Fin n) (d : Fin 71)
    (h : Q54.DepthZero n m (d.val+1) a) :
    ∃ f : SpiderVertex n m 71 → Nat,
      Graceful (spiderGraph n m 71) (71*n+m) f ∧ f (.arm a d)=0 := by
  rcases h with ⟨hlt,f,hf,hz⟩
  have he : (⟨d.val+1-1,hlt⟩ : Fin 71)=d := by
    apply Fin.ext
    change d.val+1-1=d.val
    omega
  exact ⟨f,hf,by simpa only [he] using hz⟩

theorem arm_depth_zero (n m : Nat) (hn : 2≤n) (a : Fin n) (d : Fin 71) :
    ∃ f : SpiderVertex n m 71 → Nat,
      Graceful (spiderGraph n m 71) (71*n+m) f ∧ f (.arm a d)=0 := by
  have hd := d.isLt
  by_cases hlow : d.val+1≤57
  · apply arm_from_depth n m a d
    exact K71Catalog.low_actual n m (d.val+1) hn a ⟨by omega,hlow⟩
  by_cases hq24 : d.val+1≤64
  · apply arm_from_depth n m a d
    obtain ⟨hlt,f,hf,hz⟩ := Q24Seed5Mix.combined_interval_actual 2 n m (d.val+1)
      hn a ⟨by omega,by omega⟩
    exact ⟨by omega,f,by simpa [Nat.mul_comm] using hf,hz⟩
  by_cases hq54 : d.val+1≤68
  · apply arm_from_depth n m a d
    exact Q54.selected_actual n m (d.val+1) hn a (by omega)
  by_cases htail : d.val+1≤70
  · apply arm_from_depth n m a d
    exact K71Catalog.tail_actual n m (d.val+1) hn a (by omega)
  have he : d = ⟨70,by decide⟩ := by
    apply Fin.ext
    change d.val=70
    omega
  rw [he]
  simpa [Nat.mul_comm] using (K71Tip.tips_prescribed_zero n m (by omega) a).1

/-- Full fixed-length theorem for every actual named target in S(71^n,1^m). -/
theorem all_vertices (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 71) :
    ∃ f : SpiderVertex n m 71 → Nat,
      Graceful (spiderGraph n m 71) (71*n+m) f ∧ f v=0 := by
  cases v with
  | center => exact K71Boundary.center_zero n m
  | leaf a => exact K71Boundary.leaf_zero n m a
  | arm a d => exact arm_depth_zero n m hn a d

end GracefulBoundary.K71Full

#print axioms GracefulBoundary.K71Full.arm_depth_zero
#print axioms GracefulBoundary.K71Full.all_vertices
