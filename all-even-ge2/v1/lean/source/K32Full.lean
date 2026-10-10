import K32Packets
namespace GracefulBoundary.FullFixed32

theorem k32_prefix_value : GapFill.depthPrefix 32=11 := by decide

/-- Exact fixed-k32 split: four midpoint-alpha targets plus the supplied finite middle packet band. -/
theorem k32_every_arm_vertex (n m : Nat) (hn : 2≤n) (a : Fin n) (d : Fin 32) :
    ∃f : SpiderVertex n m 32 → Nat, Graceful (spiderGraph n m 32) (n*32+m) f ∧ f (.arm a d)=0 := by
  by_cases one : d.val=0
  · have eq : d=⟨0,by decide⟩ := Fin.ext one
    rw [eq]; exact FullFixed.depth_one_zero 16 n m (by decide) hn a
  by_cases tip : d.val=31
  · have eq : d=⟨31,by decide⟩ := Fin.ext tip
    rw [eq]; exact k32_tip_zero n m hn a
  by_cases hprefix : d.val+1≤11
  · obtain ⟨hlt,f,hf,hz⟩ := GapFill.all_lengths_prefix_zero 32 n m (d.val+1) (by decide) hn a (by rw [k32_prefix_value]; exact ⟨by omega,hprefix⟩)
    have eq : (⟨d.val+1-1,hlt⟩ : Fin 32)=d := Fin.ext (by dsimp only; omega)
    rw [eq] at hz; exact ⟨f,hf,hz⟩
  by_cases near : 24≤d.val+1
  · obtain ⟨hlt,f,hf,hz⟩ := EvenBoundary.all_even_eight_depths_n_ge_two 32 n m (d.val+1) (by decide) (by decide) hn ⟨near,by omega⟩ a
    have eq : (⟨d.val+1-1,hlt⟩ : Fin 32)=d := Fin.ext (by dsimp only; omega)
    rw [eq] at hz; exact ⟨f,hf,hz⟩
  by_cases alpha : d.val+1≤15
  · have mid : d.val=11 ∨ d.val=12 ∨ d.val=13 ∨ d.val=14 := by omega
    rcases mid with h|h|h|h
    · have eq : d=⟨11,by decide⟩ := Fin.ext h; rw [eq]; exact (k32_depth12_and13 n m hn a).1
    · have eq : d=⟨12,by decide⟩ := Fin.ext h; rw [eq]; exact (k32_depth12_and13 n m hn a).2
    · have eq : d=⟨13,by decide⟩ := Fin.ext h; rw [eq]; exact (k32_depth14_and15 n m hn a).1
    · have eq : d=⟨14,by decide⟩ := Fin.ext h; rw [eq]; exact (k32_depth14_and15 n m hn a).2
  have deficit : 9≤32-(d.val+1) ∧ 32-(d.val+1)≤16 := by omega
  obtain ⟨c,hc⟩ := k32_packet_band (32-(d.val+1)) deficit
  obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider 16 n m (32-(d.val+1)) (by decide) hn c hc a
  have eq : (⟨32-(32-(d.val+1))-1,hlt⟩ : Fin 32)=d := Fin.ext (by dsimp only; omega)
  rw [eq] at hz; exact ⟨f,hf,hz⟩

theorem k32_full_zero_rotatability (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 32) :
    ∃f : SpiderVertex n m 32 → Nat, Graceful (spiderGraph n m 32) (n*32+m) f ∧ f v=0 := by
  cases v with
  | center => exact FullFixed.center_zero 16 n m (by decide)
  | arm a d => exact k32_every_arm_vertex n m hn a d
  | leaf a => exact FullFixed.short_leaf_zero 16 n m (by decide) a

theorem k32_full_unique_zero (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 32) :
    ∃f : SpiderVertex n m 32 → Nat, Graceful (spiderGraph n m 32) (n*32+m) f ∧ f v=0 ∧ ∀w,w≠v → 0<f w := by
  obtain ⟨f,hf,hz⟩ := k32_full_zero_rotatability n m hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have nonzero : f w≠0 := by intro h; exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.FullFixed32
