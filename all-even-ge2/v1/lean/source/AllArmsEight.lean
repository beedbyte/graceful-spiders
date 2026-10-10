import NamedLeavesEight
namespace GracefulBoundary.FixedEven

theorem even_shell_graph (n m : Nat) : LabelOne.graph (spiderGraph n m 8) .center 4=graph (spiderGraph n m 8) .center 8 := by
  change IndexedGraph.mk _ _ = IndexedGraph.mk _ _
  congr 1 <;> funext e <;> cases e <;> rfl

theorem eight_last_arm (h m : Nat) (hh : 2≤h) :
    ∃ f : SpiderVertex (h+1) m 8 → Nat, Graceful (spiderGraph (h+1) m 8) (8*(h+1)+m) f ∧
      f (.arm ⟨h,by omega⟩ ⟨5,by omega⟩)=0 := by
  obtain ⟨g,hg,hr⟩ := Leaf.all_center_one_eight_with_leaves h m hh
  obtain ⟨f,hf,hz⟩ := LabelOne.even_root_one_attachment (spiderGraph h m 8) .center (8*h+m) 4 (by omega) g hg hr
  rw [even_shell_graph] at hf
  have size : 8*h+m+2*4=8*(h+1)+m := by omega
  rw [size] at hf
  refine ⟨fun v => f (Append.toV h m 8 v),Append.graceful_actual h m 8 (8*(h+1)+m) f hf,?_⟩
  simpa only [Append.toV,Nat.lt_irrefl,dite_false] using hz

/-- Actual graph theorem, fixed k=8, unbounded long-arm and short-leaf counts. -/
theorem all_arm_counts_eight_near_tip (n m : Nat) (hn : 3≤n) (a : Fin n) :
    ∃ f : SpiderVertex n m 8 → Nat, Graceful (spiderGraph n m 8) (n*8+m) f ∧
      f (.arm a ⟨5,by omega⟩)=0 := by
  obtain ⟨h,rfl⟩ : ∃h,n=h+1 := ⟨n-1,by omega⟩
  obtain ⟨f,hf,hz⟩ := eight_last_arm h m (by omega)
  let z : Fin (h+1) := ⟨h,by omega⟩
  have size : 8*(h+1)+m=(h+1)*8+m := by omega
  rw [size] at hf
  exact ⟨fun v => f (NearTip.swapVertex a z v),NearTip.graceful_swap a z f hf,by simpa only [NearTip.swapVertex,NearTip.swapIndex_first] using hz⟩

end GracefulBoundary.FixedEven
