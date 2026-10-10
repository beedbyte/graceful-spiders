import UniformArm
namespace GracefulBoundary.EvenUniform
open FixedEven

theorem new_arm_bridge_weight {V E : Type} (G : IndexedGraph V E) (root : V) (g : V → Nat)
    (n r : Nat) (hn : 2≤n) (hr : 1≤r) (hroot : g root=1) :
    weight (FixedEven.graph G root (2*r)) (label g (cut n r) (2*r) (armLabel n r)) (.inr ⟨0,by omega⟩)=bridge n r := by
  rw [new_arm_weight_lookup G root g n r (by omega) hr hroot]
  obtain ⟨tail,shape⟩ := List.head?_eq_some_iff.mp (arm_list_first n r hr)
  rw [shape]
  change distance 1 (bridge n r+1)=bridge n r
  dsimp only [distance]; omega

theorem new_arm_cuts {V E : Type} (G : IndexedGraph V E) (root : V) (g : V → Nat)
    (n r : Nat) (hn : 2≤n) (hr : 1≤r) (hroot : g root=1) (d : Fin (2*r)) :
    cuts (cut (n+1) r)
      ((label g (cut n r) (2*r) (armLabel n r)) ((FixedEven.graph G root (2*r)).source (.inr d)))
      ((label g (cut n r) (2*r) (armLabel n r)) ((FixedEven.graph G root (2*r)).target (.inr d))) ↔
      (d.val≠0 ∨ n%2≠0) := by
  have cn : cut (n+1) r=cut n r+r := by simp only [cut,Nat.add_mul,Nat.one_mul]
  rw [cn]
  by_cases hd : d.val=0
  · dsimp only [FixedEven.graph,label]
    rw [ite_eq_left hd]
    dsimp only [shift,armLabel]
    rw [hroot,ite_eq_right (by have := cut_positive n r (by omega) hr; omega),hd]
    obtain ⟨tail,shape⟩ := List.head?_eq_some_iff.mp (arm_list_first n r hr)
    rw [shape]
    simp only [List.getD_cons_zero]
    rw [bridge_at_cut]
    dsimp only [cuts]
    have ct := cut_positive n r (by omega) hr
    repeat (any_goals (first | omega | split))
  · have len := arm_list_length n r hr
    have hc := crosses_lookup (cut n r+r) (armList n r) (arm_list_crosses n r hr) (d.val-1) (by have := d.isLt; omega)
    have eq : d.val-1+1=d.val := by omega
    rw [eq] at hc
    dsimp only [FixedEven.graph,label]
    rw [ite_eq_right hd]
    dsimp only [armLabel]
    exact ⟨fun _ => Or.inl hd,fun _ => hc⟩

theorem uniform_step_graceful {V E : Type} (G : IndexedGraph V E) (root : V) (g : V → Nat)
    (n r : Nat) (hn : 2≤n) (hr : 1≤r) (hg : Graceful G (n*(2*r)) g) (hroot : g root=1)
    (crossing : ∀e,cuts (cut n r) (g (G.source e)) (g (G.target e)) ↔ gains (2*r) (bridge n r) (weight G g e)) :
    Graceful (FixedEven.graph G root (2*r)) ((n+1)*(2*r)) (label g (cut n r) (2*r) (armLabel n r)) := by
  have ht := Nat.mul_le_mul_left n (show r≤2*r by omega)
  have hm : bridge n r%(2*r)=0 := by simp only [bridge,Nat.mul_mod_left]
  have hgraft := gap_graft G root g (n*(2*r)) (2*r) (cut n r) (bridge n r) hg (by omega) ht (bridge_bounds n r hn) hm crossing (armLabel n r) (arm_label_band n r hr) (new_arm_weights G root g n r hn hr hroot)
  simpa only [Nat.add_mul,Nat.one_mul] using hgraft

theorem uniform_step_crossing {V E : Type} (G : IndexedGraph V E) (root : V) (g : V → Nat)
    (n r : Nat) (hn : 2≤n) (hr : 1≤r) (hroot : g root=1)
    (crossing : ∀e,cuts (cut n r) (g (G.source e)) (g (G.target e)) ↔ gains (2*r) (bridge n r) (weight G g e)) :
    ∀e,cuts (cut (n+1) r)
      ((label g (cut n r) (2*r) (armLabel n r)) ((FixedEven.graph G root (2*r)).source e))
      ((label g (cut n r) (2*r) (armLabel n r)) ((FixedEven.graph G root (2*r)).target e)) ↔
      gains (2*r) (bridge (n+1) r) (weight (FixedEven.graph G root (2*r)) (label g (cut n r) (2*r) (armLabel n r)) e) := by
  intro e; cases e with
  | inl e =>
    have hw : weight (FixedEven.graph G root (2*r)) (label g (cut n r) (2*r) (armLabel n r)) (.inl e)=gapWeight (2*r) (bridge n r) (weight G g e) := by
      dsimp only [weight,FixedEven.graph,label]
      rw [shifted_distance]
      change (if cuts (cut n r) (g (G.source e)) (g (G.target e)) then weight G g e+2*r else weight G g e)=gapWeight (2*r) (bridge n r) (weight G g e)
      simp only [gapWeight,←crossing e]
    rw [hw,gains_shift _ _ _ _ (bridge_next_bounds n r)]
    dsimp only [FixedEven.graph,label]
    rw [show cut (n+1) r=cut n r+r by simp only [cut,Nat.add_mul,Nat.one_mul],shifted_cuts _ (2*r) r _ _ (by omega)]
    exact crossing e
  | inr d =>
    rw [new_arm_cuts G root g n r hn hr hroot d]
    by_cases hd : d.val=0
    · have de : d=⟨0,by omega⟩ := Fin.ext hd
      rw [de,new_arm_bridge_weight G root g n r hn hr hroot]
      have hm : bridge n r%(2*r)=0 := by simp only [bridge,Nat.mul_mod_left]
      dsimp only [gains]
      rw [hm,bridge_next]
      repeat (any_goals (first | omega | split))
    · have hw := new_arm_weights G root g n r hn hr hroot
      have bounds : 1≤weight (FixedEven.graph G root (2*r)) (label g (cut n r) (2*r) (armLabel n r)) (.inr d) ∧
          weight (FixedEven.graph G root (2*r)) (label g (cut n r) (2*r) (armLabel n r)) (.inr d)<2*r := by
        rcases hw.shape d with h|h
        · have eq := hw.injective d ⟨0,by omega⟩ (h.trans (new_arm_bridge_weight G root g n r hn hr hroot).symm)
          have val := congrArg Fin.val eq; dsimp only at val; contradiction
        · exact h
      have hm := Nat.mod_eq_of_lt bounds.2
      dsimp only [gains]
      rw [hm]
      omega

end GracefulBoundary.EvenUniform
