import UniformLeaves
namespace GracefulBoundary.EvenUniform
open FixedEven

theorem all_even_anchored_alpha (k : Nat) (hk : 6≤k) (heven : k%2=0) :
    ∃ f : Fin (2*k+1) → Nat, Graceful (pathGraph (2*k)) (2*k) f ∧ Alpha (pathGraph (2*k)) k f ∧
      f ⟨k,by omega⟩=1 ∧ f ⟨k+1,by omega⟩=2*k ∧ f ⟨k+2,by omega⟩=0 := by
  obtain ⟨r,hr,rfl⟩ : ∃r,3≤r ∧ k=2*r := ⟨k/2,by omega,by omega⟩
  exact all_anchored_alpha_paths r hr

theorem shell_base3 : LabelOne.Packet 3 [4,1,2,2,0,0,1] := LabelOne.base3_valid
theorem shell_base4 : LabelOne.Packet 4 [5,2,2,3,3,0,0,1,1] :=
  LabelOne.step_valid 2 (by omega) LabelOne.base2 LabelOne.base2_valid
theorem uniform_shell_step (r : Nat) (hr : 3≤r) (c : List Nat) (hc : LabelOne.Packet r c) :
    LabelOne.Packet (r+2) (LabelOne.step r c) := LabelOne.step_valid r (by omega) c hc
theorem uniform_shells (r : Nat) (hr : 3≤r) : ∃c,LabelOne.Packet r c := LabelOne.packets r (by omega)

theorem even_shell_graph (h m r : Nat) : LabelOne.graph (spiderGraph h m (2*r)) .center r=FixedEven.graph (spiderGraph h m (2*r)) .center (2*r) := by
  change IndexedGraph.mk _ _ = IndexedGraph.mk _ _
  congr 1 <;> funext e <;> cases e <;> rfl

theorem all_even_last_arm (r h m : Nat) (hr : 3≤r) (hh : 2≤h) :
    ∃ f : SpiderVertex (h+1) m (2*r) → Nat, Graceful (spiderGraph (h+1) m (2*r)) ((h+1)*(2*r)+m) f ∧
      f (.arm ⟨h,by omega⟩ ⟨2*r-3,by omega⟩)=0 := by
  obtain ⟨g,hg,hroot⟩ := all_center_one_even_with_leaves r h m hr hh
  obtain ⟨f,hf,hz⟩ := LabelOne.even_root_one_attachment (spiderGraph h m (2*r)) .center (h*(2*r)+m) r (by omega) g hg hroot
  rw [even_shell_graph] at hf
  have size : h*(2*r)+m+2*r=(h+1)*(2*r)+m := by simp only [Nat.add_mul,Nat.one_mul,Nat.add_right_comm]
  rw [size] at hf
  refine ⟨fun v => f (FixedEven.Append.toV h m (2*r) v),FixedEven.Append.graceful_actual h m (2*r) ((h+1)*(2*r)+m) f hf,?_⟩
  simpa only [FixedEven.Append.toV,Nat.lt_irrefl,dite_false] using hz

theorem all_even_selected_arm (r n m : Nat) (hr : 3≤r) (hn : 3≤n) (a : Fin n) :
    ∃ f : SpiderVertex n m (2*r) → Nat, Graceful (spiderGraph n m (2*r)) (n*(2*r)+m) f ∧
      f (.arm a ⟨2*r-3,by omega⟩)=0 := by
  obtain ⟨h,rfl⟩ : ∃h,n=h+1 := ⟨n-1,by omega⟩
  obtain ⟨f,hf,hz⟩ := all_even_last_arm r h m hr (by omega)
  let z : Fin (h+1) := ⟨h,by omega⟩
  exact ⟨fun v => f (NearTip.swapVertex a z v),NearTip.graceful_swap a z f hf,by simpa only [NearTip.swapVertex,NearTip.swapIndex_first] using hz⟩

/-- Complete actual named graph theorem, all even k>=6, all n>=3, all m>=0. -/
theorem all_even_near_tip (k n m : Nat) (hk : 6≤k) (heven : k%2=0) (hn : 3≤n) (a : Fin n) :
    ∃ f : SpiderVertex n m k → Nat, Graceful (spiderGraph n m k) (n*k+m) f ∧
      f (.arm a ⟨k-3,by omega⟩)=0 := by
  obtain ⟨r,hr,rfl⟩ : ∃r,3≤r ∧ k=2*r := ⟨k/2,by omega,by omega⟩
  exact all_even_selected_arm r n m hr hn a

end GracefulBoundary.EvenUniform
