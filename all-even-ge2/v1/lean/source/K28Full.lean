import K28Packets
namespace GracefulBoundary.FullFixed28

theorem k28_prefix_value : GapFill.depthPrefix 28=11 := by decide
theorem k28_every_arm_vertex (n m : Nat) (hn : 2≤n) (a : Fin n) (d : Fin 28) :
    ∃f : SpiderVertex n m 28 → Nat, Graceful (spiderGraph n m 28) (n*28+m) f ∧ f (.arm a d)=0 := by
  by_cases one : d.val=0
  · have eq : d=⟨0,by decide⟩ := Fin.ext one
    rw [eq]; exact FullFixed.depth_one_zero 14 n m (by decide) hn a
  by_cases tip : d.val=27
  · have eq : d=⟨27,by decide⟩ := Fin.ext tip
    rw [eq]; exact k28_tip_zero n m hn a
  by_cases hprefix : d.val+1≤11
  · obtain ⟨hlt,f,hf,hz⟩ := GapFill.all_lengths_prefix_zero 28 n m (d.val+1) (by decide) hn a (by rw [k28_prefix_value]; exact ⟨by omega,hprefix⟩)
    have eq : (⟨d.val+1-1,hlt⟩ : Fin 28)=d := Fin.ext (by dsimp only; omega)
    rw [eq] at hz; exact ⟨f,hf,hz⟩
  by_cases near : 20≤d.val+1
  · obtain ⟨hlt,f,hf,hz⟩ := EvenBoundary.all_even_eight_depths_n_ge_two 28 n m (d.val+1) (by decide) (by decide) hn ⟨near,by omega⟩ a
    have eq : (⟨d.val+1-1,hlt⟩ : Fin 28)=d := Fin.ext (by dsimp only; omega)
    rw [eq] at hz; exact ⟨f,hf,hz⟩
  have mid : d.val=11 ∨ d.val=12 ∨ d.val=13 ∨ d.val=14 ∨ d.val=15 ∨ d.val=16 ∨ d.val=17 ∨ d.val=18 := by omega
  rcases mid with h|h|h|h|h|h|h|h
  · have eq : d=⟨11,by decide⟩ := Fin.ext h; rw [eq]; exact k28_depth12 n m hn a
  · have eq : d=⟨12,by decide⟩ := Fin.ext h; rw [eq]; exact k28_depth13 n m hn a
  · have eq : d=⟨13,by decide⟩ := Fin.ext h; rw [eq]; exact k28_depth14 n m hn a
  · have eq : d=⟨14,by decide⟩ := Fin.ext h; rw [eq]; exact k28_depth15 n m hn a
  · have eq : d=⟨15,by decide⟩ := Fin.ext h; rw [eq]; exact k28_depth16 n m hn a
  · have eq : d=⟨16,by decide⟩ := Fin.ext h; rw [eq]; exact k28_depth17 n m hn a
  · have eq : d=⟨17,by decide⟩ := Fin.ext h; rw [eq]; exact k28_depth18 n m hn a
  · have eq : d=⟨18,by decide⟩ := Fin.ext h; rw [eq]; exact k28_depth19 n m hn a

theorem k28_full_zero_rotatability (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 28) :
    ∃f : SpiderVertex n m 28 → Nat, Graceful (spiderGraph n m 28) (n*28+m) f ∧ f v=0 := by
  cases v with
  | center => exact FullFixed.center_zero 14 n m (by decide)
  | arm a d => exact k28_every_arm_vertex n m hn a d
  | leaf a => exact FullFixed.short_leaf_zero 14 n m (by decide) a

theorem k28_full_unique_zero (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 28) :
    ∃f : SpiderVertex n m 28 → Nat, Graceful (spiderGraph n m 28) (n*28+m) f ∧ f v=0 ∧ ∀w,w≠v → 0<f w := by
  obtain ⟨f,hf,hz⟩ := k28_full_zero_rotatability n m hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have nonzero : f w≠0 := by intro h; exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.FullFixed28
