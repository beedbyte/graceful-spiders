import TipFixed
namespace GracefulBoundary.FullFixed

theorem fixed_depth_one_zero (k n m : Nat) (hk : k=20 ∨ k=22) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m k → Nat, Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨0,by omega⟩)=0 := by
  rcases hk with hk|hk <;> subst k
  · exact depth_one_zero 10 n m (by decide) hn a
  · exact depth_one_zero 11 n m (by decide) hn a

theorem fixed_prefix_value (k : Nat) (hk : k=20 ∨ k=22) : GapFill.depthPrefix k=11 := by
  rcases hk with hk|hk <;> subst k <;> decide

theorem fixed_prefix_zero (k n m : Nat) (hk : k=20 ∨ k=22) (hn : 2≤n) (a : Fin n) (d : Fin k)
    (hd : 2≤d.val+1 ∧ d.val+1≤11) :
    ∃f : SpiderVertex n m k → Nat, Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a d)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := GapFill.all_lengths_prefix_zero k n m (d.val+1) (by omega) hn a
    (by rw [fixed_prefix_value k hk]; exact hd)
  have eq : (⟨d.val+1-1,hlt⟩ : Fin k)=d := Fin.ext (by dsimp only; omega)
  rw [eq] at hz; exact ⟨f,hf,hz⟩

/-- Exact gap-free depth case split, with no unsupported interval inference. -/
theorem fixed_every_arm_vertex (k n m : Nat) (hk : k=20 ∨ k=22) (hn : 2≤n) (a : Fin n) (d : Fin k) :
    ∃f : SpiderVertex n m k → Nat, Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a d)=0 := by
  by_cases one : d.val=0
  · have eq : d=⟨0,by omega⟩ := Fin.ext one
    rw [eq]; exact fixed_depth_one_zero k n m hk hn a
  by_cases tip : d.val=k-1
  · have eq : d=⟨k-1,by omega⟩ := Fin.ext tip
    rw [eq]; exact fixed_tip_zero k n m hk hn a
  by_cases hprefix : d.val+1≤11
  · exact fixed_prefix_zero k n m hk hn a d ⟨by omega,hprefix⟩
  by_cases near : k-8≤d.val+1
  · obtain ⟨hlt,f,hf,hz⟩ := EvenBoundary.all_even_eight_depths_n_ge_two k n m (d.val+1) (by omega)
      (by rcases hk with h|h <;> subst k <;> decide) hn ⟨near,by omega⟩ a
    have eq : (⟨d.val+1-1,hlt⟩ : Fin k)=d := Fin.ext (by dsimp only; omega)
    rw [eq] at hz; exact ⟨f,hf,hz⟩
  have twenty_two : k=22 := by omega
  subst k
  have middle : d.val=11 ∨ d.val=12 := by omega
  rcases middle with h|h
  · have eq : d=⟨11,by decide⟩ := Fin.ext h
    subst d; exact k22_depth12 n m hn a
  · have eq : d=⟨12,by decide⟩ := Fin.ext h
    subst d; exact k22_depth13 n m hn a

/-- Every actual named vertex request, with a separate graceful labeling per request. -/
theorem fixed_full_zero_rotatability (k n m : Nat) (hk : k=20 ∨ k=22) (hn : 2≤n)
    (v : SpiderVertex n m k) :
    ∃f : SpiderVertex n m k → Nat, Graceful (spiderGraph n m k) (n*k+m) f ∧ f v=0 := by
  cases v with
  | center =>
    rcases hk with h|h <;> subst k
    · exact center_zero 10 n m (by decide)
    · exact center_zero 11 n m (by decide)
  | arm a d => exact fixed_every_arm_vertex k n m hk hn a d
  | leaf a =>
    rcases hk with h|h <;> subst k
    · exact short_leaf_zero 10 n m (by decide) a
    · exact short_leaf_zero 11 n m (by decide) a

theorem fixed_full_unique_zero (k n m : Nat) (hk : k=20 ∨ k=22) (hn : 2≤n)
    (v : SpiderVertex n m k) :
    ∃f : SpiderVertex n m k → Nat, Graceful (spiderGraph n m k) (n*k+m) f ∧ f v=0 ∧ ∀w,w≠v → 0<f w := by
  obtain ⟨f,hf,hz⟩ := fixed_full_zero_rotatability k n m hk hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have nonzero : f w≠0 := by intro h; exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

/-- Negative quantifier control: two distinct named vertices cannot share zero in one labeling. -/
theorem no_two_distinct_zeros (k n m : Nat) (f : SpiderVertex n m k → Nat)
    (hf : Graceful (spiderGraph n m k) (n*k+m) f) (v w : SpiderVertex n m k) (hne : v≠w) :
    ¬(f v=0 ∧ f w=0) := by
  intro h; exact hne (hf.vertices.injective v w (h.1.trans h.2.symm))

theorem no_short_leaf_when_m_zero (k n : Nat) : ¬∃a : Fin 0,(SpiderVertex.leaf a : SpiderVertex n 0 k)=.leaf a := by
  rintro ⟨a,_⟩; exact Fin.elim0 a

theorem fixed_k_domain_rejects_others (k : Nat) (hk : k≠20 ∧ k≠22) : ¬(k=20 ∨ k=22) := by omega

end GracefulBoundary.FullFixed
