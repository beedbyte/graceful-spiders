import GapDepth
import EightDepthTheorem
namespace GracefulBoundary.FullFixed

theorem center_zero (r n m : Nat) (hr : 0<r) :
    ∃f : SpiderVertex n m (2*r) → Nat, Graceful (spiderGraph n m (2*r)) (n*(2*r)+m) f ∧ f .center=0 :=
  ⟨residualLabel n m (2*r),EvenResidual.residual_gracefulness n m r hr,rfl⟩

def swapLeafV {n m k : Nat} (a b : Fin m) : SpiderVertex n m k → SpiderVertex n m k
  | .center => .center
  | .arm i d => .arm i d
  | .leaf j => .leaf (NearTip.swapIndex a b j)
def swapLeafE {n m k : Nat} (a b : Fin m) : SpiderEdge n m k → SpiderEdge n m k
  | .arm i d => .arm i d
  | .leaf j => .leaf (NearTip.swapIndex a b j)

theorem leaf_vertex_involution {n m k : Nat} (a b : Fin m) (v : SpiderVertex n m k) :
    swapLeafV a b (swapLeafV a b v)=v := by cases v <;> simp only [swapLeafV,NearTip.swapIndex_involution]
theorem leaf_edge_involution {n m k : Nat} (a b : Fin m) (e : SpiderEdge n m k) :
    swapLeafE a b (swapLeafE a b e)=e := by cases e <;> simp only [swapLeafE,NearTip.swapIndex_involution]
theorem leaf_weights {n m k : Nat} (a b : Fin m) (f : SpiderVertex n m k → Nat) (e : SpiderEdge n m k) :
    weight (spiderGraph n m k) (fun v => f (swapLeafV a b v)) e=weight (spiderGraph n m k) f (swapLeafE a b e) := by
  cases e with
  | leaf j => rfl
  | arm i d => by_cases hd : d.val=0 <;> simp only [weight,spiderGraph,swapLeafV,swapLeafE,hd,ite_true,ite_false]
theorem graceful_leaf_swap {n m k N : Nat} (a b : Fin m) (f : SpiderVertex n m k → Nat)
    (hf : Graceful (spiderGraph n m k) N f) : Graceful (spiderGraph n m k) N (fun v => f (swapLeafV a b v)) := by
  constructor
  · exact NearTip.band_transport f 0 N hf.vertices (swapLeafV a b) (swapLeafV a b) (leaf_vertex_involution a b) (leaf_vertex_involution a b)
  · have hb := NearTip.band_transport (weight (spiderGraph n m k) f) 1 N hf.edges (swapLeafE a b) (swapLeafE a b) (leaf_edge_involution a b) (leaf_edge_involution a b)
    rw [funext (leaf_weights a b f)]; exact hb

/-- Every existing short leaf, including any name; Fin m makes the m=0 case vacuous. -/
theorem short_leaf_zero (r n m : Nat) (hr : 0<r) (a : Fin m) :
    ∃f : SpiderVertex n m (2*r) → Nat, Graceful (spiderGraph n m (2*r)) (n*(2*r)+m) f ∧ f (.leaf a)=0 := by
  let z : Fin m := ⟨m-1,by have := a.isLt; omega⟩
  let g := residualLabel n m (2*r)
  have hg := EvenResidual.residual_gracefulness n m r hr
  have hz : g (.leaf z)=n*(2*r)+m := by dsimp [g,residualLabel,z]; have := a.isLt; omega
  let f := fun v => g (swapLeafV a z v)
  have hf : Graceful (spiderGraph n m (2*r)) (n*(2*r)+m) f := graceful_leaf_swap a z g hg
  have hm : f (.leaf a)=n*(2*r)+m := by simpa only [f,swapLeafV,NearTip.swapIndex_first] using hz
  exact ⟨complementLabel (n*(2*r)+m) f,whole_graph_graceful_complement _ _ f hf,complement_maximum_zero _ f _ hm⟩

theorem center_one_maximum_with_leaves (r n m : Nat) (hr : 3≤r) (hn : 2≤n) :
    ∃f : SpiderVertex n m (2*r) → Nat, Graceful (spiderGraph n m (2*r)) (n*(2*r)+m) f ∧
      f (.arm ⟨1,by omega⟩ ⟨0,by omega⟩)=n*(2*r)+m := by
  obtain ⟨g,hg⟩ := EvenUniform.uniform_residual_states r n hr hn
  have hq : 2≤n*(2*r) := by
    have h := Nat.mul_le_mul_left n (show 1≤2*r by omega); simp only [Nat.mul_one] at h; omega
  have hf := FixedEven.maximum_leaf_extension (spiderGraph n 0 (2*r)) (n*(2*r)) m g hg.graceful .center
    (.arm ⟨1,by omega⟩ ⟨0,by omega⟩) (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)
    (.arm ⟨1,by omega⟩ ⟨0,by omega⟩) (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)
    (EvenUniform.actual_maximum_anchor n (2*r) hn (by omega)) hg.root hg.maximum hg.zero hq
  refine ⟨fun v => CenterLeaves.insertLabel g (n*(2*r)) m (FixedEven.Leaf.toV n m (2*r) v),FixedEven.Leaf.graceful_actual n m (2*r) (n*(2*r)+m) _ hf.1,?_⟩
  dsimp only [FixedEven.Leaf.toV,CenterLeaves.insertLabel]
  rw [hg.maximum,ite_eq_left (by omega)]

theorem depth_one_zero (r n m : Nat) (hr : 3≤r) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m (2*r) → Nat, Graceful (spiderGraph n m (2*r)) (n*(2*r)+m) f ∧ f (.arm a ⟨0,by omega⟩)=0 := by
  obtain ⟨g,hg,hm⟩ := center_one_maximum_with_leaves r n m hr hn
  let z : Fin n := ⟨1,by omega⟩
  let f := fun v => g (NearTip.swapVertex a z v)
  have hf : Graceful (spiderGraph n m (2*r)) (n*(2*r)+m) f := NearTip.graceful_swap a z g hg
  have maximum : f (.arm a ⟨0,by omega⟩)=n*(2*r)+m := by simpa only [f,NearTip.swapVertex,NearTip.swapIndex_first] using hm
  exact ⟨complementLabel (n*(2*r)+m) f,whole_graph_graceful_complement _ _ f hf,complement_maximum_zero _ f _ maximum⟩

end GracefulBoundary.FullFixed
