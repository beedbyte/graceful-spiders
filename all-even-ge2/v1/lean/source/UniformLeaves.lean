import UniformState
namespace GracefulBoundary.EvenUniform
open FixedEven
theorem actual_maximum_anchor (n k : Nat) (hn : 2≤n) (hk : 2≤k) :
    MaximumAnchor (spiderGraph n 0 k) .center
      (.arm ⟨1,by omega⟩ ⟨0,by omega⟩) (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)
      (.arm ⟨1,by omega⟩ ⟨0,by omega⟩) (.arm ⟨1,by omega⟩ ⟨1,by omega⟩) := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · intro e; cases e with
    | leaf j => exact Fin.elim0 j
    | arm i d =>
      by_cases hc : i.val=1 ∧ d.val=0
      · left; congr 1 <;> apply Fin.ext <;> dsimp only <;> omega
      · by_cases hz : i.val=1 ∧ d.val=1
        · right; left; congr 1 <;> apply Fin.ext <;> dsimp only <;> omega
        · right; right; constructor
          · dsimp only [spiderGraph]; split
            · intro he; cases he
            · intro he
              have ⟨hi,hd⟩ := SpiderVertex.arm.inj he
              have idx := congrArg Fin.val hi
              have dep := congrArg Fin.val hd
              dsimp only at idx dep
              omega
          · intro he
            have ⟨hi,hd⟩ := SpiderVertex.arm.inj he
            have idx := congrArg Fin.val hi
            have dep := congrArg Fin.val hd
            dsimp only at idx dep
            omega

theorem all_center_one_even_with_leaves (r n m : Nat) (hr : 3≤r) (hn : 2≤n) :
    ∃ f : SpiderVertex n m (2*r) → Nat, Graceful (spiderGraph n m (2*r)) (n*(2*r)+m) f ∧ f .center=1 := by
  obtain ⟨g,hg⟩ := uniform_residual_states r n hr hn
  have hq : 2≤n*(2*r) := by
    have h := Nat.mul_le_mul_left n (show 1≤2*r by omega)
    simp only [Nat.mul_one] at h
    omega
  have hf := maximum_leaf_extension (spiderGraph n 0 (2*r)) (n*(2*r)) m g hg.graceful .center
    (.arm ⟨1,by omega⟩ ⟨0,by omega⟩) (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)
    (.arm ⟨1,by omega⟩ ⟨0,by omega⟩) (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)
    (actual_maximum_anchor n (2*r) hn (by omega)) hg.root hg.maximum hg.zero hq
  exact ⟨fun v => CenterLeaves.insertLabel g (n*(2*r)) m (FixedEven.Leaf.toV n m (2*r) v),FixedEven.Leaf.graceful_actual n m (2*r) (n*(2*r)+m) _ hf.1,hf.2⟩

end GracefulBoundary.EvenUniform
