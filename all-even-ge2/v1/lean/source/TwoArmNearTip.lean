import OneArmNamed
namespace GracefulBoundary.EvenBoundary
open EvenUniform

theorem nonempty_even_residual (r h m : Nat) (hr : 3≤r) (hh : 1≤h) :
    ∃g : SpiderVertex h m (2*r) → Nat, Graceful (spiderGraph h m (2*r)) (h*(2*r)+m) g ∧ g .center=1 := by
  by_cases one : h=1
  · subst h; simpa only [Nat.one_mul] using Single.all_one_arm_center_one r m hr
  · exact all_center_one_even_with_leaves r h m hr (by omega)

theorem near_tip_last_arm (r h m : Nat) (hr : 3≤r) (hh : 1≤h) :
    ∃f : SpiderVertex (h+1) m (2*r) → Nat, Graceful (spiderGraph (h+1) m (2*r)) ((h+1)*(2*r)+m) f ∧
      f (.arm ⟨h,by omega⟩ ⟨2*r-3,by omega⟩)=0 := by
  obtain ⟨g,hg,hroot⟩ := nonempty_even_residual r h m hr hh
  obtain ⟨f,hf,hzero⟩ := LabelOne.even_root_one_attachment (spiderGraph h m (2*r)) .center (h*(2*r)+m) r (by omega) g hg hroot
  rw [EvenUniform.even_shell_graph] at hf
  have size : h*(2*r)+m+2*r=(h+1)*(2*r)+m := by simp only [Nat.add_mul,Nat.one_mul,Nat.add_right_comm]
  rw [size] at hf
  exact ⟨fun v => f (FixedEven.Append.toV h m (2*r) v),FixedEven.Append.graceful_actual h m (2*r) ((h+1)*(2*r)+m) f hf,by simpa only [FixedEven.Append.toV,Nat.lt_irrefl,dite_false] using hzero⟩

theorem all_even_near_tip_n_ge_two (k n m : Nat) (hk : 6≤k) (heven : k%2=0) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m k → Nat, Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨k-3,by omega⟩)=0 := by
  obtain ⟨r,hr,rfl⟩ : ∃r,3≤r ∧ k=2*r := ⟨k/2,by omega,by omega⟩
  obtain ⟨h,rfl⟩ : ∃h,n=h+1 := ⟨n-1,by omega⟩
  obtain ⟨f,hf,hzero⟩ := near_tip_last_arm r h m hr (by omega)
  let z : Fin (h+1) := ⟨h,by omega⟩
  exact ⟨fun v => f (NearTip.swapVertex a z v),NearTip.graceful_swap a z f hf,by simpa only [NearTip.swapVertex,NearTip.swapIndex_first] using hzero⟩

/-- Center-specific actual two-arm theorem, including every short-leaf count. -/
theorem actual_two_arm_near_tip (k m : Nat) (hk : 6≤k) (heven : k%2=0) (a : Fin 2) :
    ∃f : SpiderVertex 2 m k → Nat, Graceful (spiderGraph 2 m k) (2*k+m) f ∧ f (.arm a ⟨k-3,by omega⟩)=0 :=
  all_even_near_tip_n_ge_two k 2 m hk heven (by omega) a

end GracefulBoundary.EvenBoundary
