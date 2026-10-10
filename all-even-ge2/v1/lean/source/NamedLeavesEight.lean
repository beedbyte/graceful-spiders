import MaximumLeaves
namespace GracefulBoundary.FixedEven.Leaf

def toV (n m k : Nat) : SpiderVertex n m k → Sum (SpiderVertex n 0 k) (Fin m)
  | .center => .inl .center
  | .arm i d => .inl (.arm i d)
  | .leaf j => .inr j
def fromV (n m k : Nat) : Sum (SpiderVertex n 0 k) (Fin m) → SpiderVertex n m k
  | .inl .center => .center
  | .inl (.arm i d) => .arm i d
  | .inl (.leaf j) => Fin.elim0 j
  | .inr j => .leaf j
def toE (n m k : Nat) : SpiderEdge n m k → Sum (SpiderEdge n 0 k) (Fin m)
  | .arm i d => .inl (.arm i d)
  | .leaf j => .inr j
def fromE (n m k : Nat) : Sum (SpiderEdge n 0 k) (Fin m) → SpiderEdge n m k
  | .inl (.arm i d) => .arm i d
  | .inl (.leaf j) => Fin.elim0 j
  | .inr j => .leaf j

theorem vertex_left_inverse (n m k : Nat) (v : SpiderVertex n m k) : fromV n m k (toV n m k v)=v := by cases v <;> rfl
theorem vertex_right_inverse (n m k : Nat) (v : Sum (SpiderVertex n 0 k) (Fin m)) : toV n m k (fromV n m k v)=v := by
  cases v with
  | inr j => rfl
  | inl v => cases v with
    | center => rfl
    | arm i d => rfl
    | leaf j => exact Fin.elim0 j
theorem edge_left_inverse (n m k : Nat) (e : SpiderEdge n m k) : fromE n m k (toE n m k e)=e := by cases e <;> rfl
theorem edge_right_inverse (n m k : Nat) (e : Sum (SpiderEdge n 0 k) (Fin m)) : toE n m k (fromE n m k e)=e := by
  cases e with
  | inr j => rfl
  | inl e => cases e with
    | arm i d => rfl
    | leaf j => exact Fin.elim0 j

theorem weights (n m k : Nat) (f : Sum (SpiderVertex n 0 k) (Fin m) → Nat) (e : SpiderEdge n m k) :
    weight (spiderGraph n m k) (fun v => f (toV n m k v)) e=
      weight (leavesGraph (spiderGraph n 0 k) .center m) f (toE n m k e) := by
  cases e with
  | leaf j => rfl
  | arm i d => by_cases hd : d.val=0 <;> simp only [weight,spiderGraph,toV,toE,leavesGraph,hd,ite_true,ite_false]

theorem graceful_actual (n m k q : Nat) (f : Sum (SpiderVertex n 0 k) (Fin m) → Nat)
    (hf : Graceful (leavesGraph (spiderGraph n 0 k) .center m) q f) :
    Graceful (spiderGraph n m k) q (fun v => f (toV n m k v)) := by
  constructor
  · exact NearTip.band_transport f 0 q hf.vertices (toV n m k) (fromV n m k) (vertex_left_inverse n m k) (vertex_right_inverse n m k)
  · have h := NearTip.band_transport (weight (leavesGraph (spiderGraph n 0 k) .center m) f) 1 q hf.edges (toE n m k) (fromE n m k) (edge_left_inverse n m k) (edge_right_inverse n m k)
    rw [funext (weights n m k f)]; exact h

theorem maximum_anchor (n : Nat) (hn : 2≤n) :
    MaximumAnchor (spiderGraph n 0 8) .center
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

theorem all_center_one_eight_with_leaves (n m : Nat) (hn : 2≤n) :
    ∃ f : SpiderVertex n m 8 → Nat, Graceful (spiderGraph n m 8) (8*n+m) f ∧ f .center=1 := by
  obtain ⟨g,hg⟩ := all_center_one_eight_residuals n hn
  have hf := maximum_leaf_extension (spiderGraph n 0 8) (8*n) m g hg.graceful .center
    (.arm ⟨1,by omega⟩ ⟨0,by omega⟩) (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)
    (.arm ⟨1,by omega⟩ ⟨0,by omega⟩) (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)
    (maximum_anchor n hn) hg.root hg.maximum hg.zero (by omega)
  exact ⟨fun v => CenterLeaves.insertLabel g (8*n) m (toV n m 8 v),graceful_actual n m 8 (8*n+m) _ hf.1,hf.2⟩

end GracefulBoundary.FixedEven.Leaf
