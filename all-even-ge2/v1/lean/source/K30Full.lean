import K30Packets
namespace GracefulBoundary.FullFixed30

theorem k30_prefix_value : GapFill.depthPrefix 30=11 := by decide

/-- Explicit fixed-k30 case split; the supplied finite packet band includes the two direct-shell cases. -/
theorem k30_every_arm_vertex (n m : Nat) (hn : 2≤n) (a : Fin n) (d : Fin 30) :
    ∃f : SpiderVertex n m 30 → Nat, Graceful (spiderGraph n m 30) (n*30+m) f ∧ f (.arm a d)=0 := by
  by_cases one : d.val=0
  · have eq : d=⟨0,by decide⟩ := Fin.ext one
    rw [eq]; exact FullFixed.depth_one_zero 15 n m (by decide) hn a
  by_cases tip : d.val=29
  · have eq : d=⟨29,by decide⟩ := Fin.ext tip
    rw [eq]; exact k30_tip_zero n m hn a
  by_cases hprefix : d.val+1≤11
  · obtain ⟨hlt,f,hf,hz⟩ := GapFill.all_lengths_prefix_zero 30 n m (d.val+1) (by decide) hn a (by rw [k30_prefix_value]; exact ⟨by omega,hprefix⟩)
    have eq : (⟨d.val+1-1,hlt⟩ : Fin 30)=d := Fin.ext (by dsimp only; omega)
    rw [eq] at hz; exact ⟨f,hf,hz⟩
  by_cases near : 22≤d.val+1
  · obtain ⟨hlt,f,hf,hz⟩ := EvenBoundary.all_even_eight_depths_n_ge_two 30 n m (d.val+1) (by decide) (by decide) hn ⟨near,by omega⟩ a
    have eq : (⟨d.val+1-1,hlt⟩ : Fin 30)=d := Fin.ext (by dsimp only; omega)
    rw [eq] at hz; exact ⟨f,hf,hz⟩
  have deficit : 9≤30-(d.val+1) ∧ 30-(d.val+1)≤18 := by omega
  obtain ⟨c,hc⟩ := k30_packet_band (30-(d.val+1)) deficit
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 15 n m (30-(d.val+1)) (by decide) hn c hc a
  have eq : (⟨30-(30-(d.val+1))-1,hlt⟩ : Fin 30)=d := Fin.ext (by dsimp only; omega)
  rw [eq] at hz; exact ⟨f,hf,hz⟩

theorem k30_full_zero_rotatability (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 30) :
    ∃f : SpiderVertex n m 30 → Nat, Graceful (spiderGraph n m 30) (n*30+m) f ∧ f v=0 := by
  cases v with
  | center => exact FullFixed.center_zero 15 n m (by decide)
  | arm a d => exact k30_every_arm_vertex n m hn a d
  | leaf a => exact FullFixed.short_leaf_zero 15 n m (by decide) a

theorem k30_full_unique_zero (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 30) :
    ∃f : SpiderVertex n m 30 → Nat, Graceful (spiderGraph n m 30) (n*30+m) f ∧ f v=0 ∧ ∀w,w≠v → 0<f w := by
  obtain ⟨f,hf,hz⟩ := k30_full_zero_rotatability n m hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have nonzero : f w≠0 := by intro h; exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.FullFixed30
