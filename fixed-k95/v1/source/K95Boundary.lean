import FiniteAlphaTransfer

namespace GracefulBoundary.K95Boundary

theorem center_zero (n m : Nat) :
    ∃ f : SpiderVertex n m 95 → Nat,
      Graceful (spiderGraph n m 95) (95*n+m) f ∧ f .center = 0 := by
  exact ⟨residualLabel n m 95,
    by simpa [Nat.mul_comm] using residual_gracefulness n m 47,rfl⟩

def swapLeafVertex {n m k : Nat} (a b : Fin m) : SpiderVertex n m k → SpiderVertex n m k
  | .center => .center
  | .arm i d => .arm i d
  | .leaf i => .leaf (swapIndex a b i)

def swapLeafEdge {n m k : Nat} (a b : Fin m) : SpiderEdge n m k → SpiderEdge n m k
  | .arm i d => .arm i d
  | .leaf i => .leaf (swapIndex a b i)

theorem swapLeafVertex_involution {n m k : Nat} (a b : Fin m) (v : SpiderVertex n m k) :
    swapLeafVertex a b (swapLeafVertex a b v) = v := by
  cases v <;> simp only [swapLeafVertex, swapIndex_involution]

theorem swapLeafEdge_involution {n m k : Nat} (a b : Fin m) (e : SpiderEdge n m k) :
    swapLeafEdge a b (swapLeafEdge a b e) = e := by
  cases e <;> simp only [swapLeafEdge, swapIndex_involution]

theorem swapLeaf_weights {n m k : Nat} (a b : Fin m) (f : SpiderVertex n m k → Nat)
    (e : SpiderEdge n m k) :
    weight (spiderGraph n m k) (fun v => f (swapLeafVertex a b v)) e =
      weight (spiderGraph n m k) f (swapLeafEdge a b e) := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    by_cases hd : d.val = 0 <;>
      simp only [weight, spiderGraph, swapLeafEdge, swapLeafVertex,
        hd, ite_true, ite_false]

theorem graceful_swapLeaf {n m k M : Nat} (a b : Fin m) (f : SpiderVertex n m k → Nat)
    (hf : Graceful (spiderGraph n m k) M f) :
    Graceful (spiderGraph n m k) M (fun v => f (swapLeafVertex a b v)) :=
  graceful_transport (spiderGraph n m k) (spiderGraph n m k) M f hf
    (swapLeafVertex a b) (swapLeafVertex a b) (swapLeafEdge a b) (swapLeafEdge a b)
    (swapLeafVertex_involution a b) (swapLeafVertex_involution a b)
    (swapLeafEdge_involution a b) (swapLeafEdge_involution a b)
    (swapLeaf_weights a b f)

theorem leaf_zero (n m : Nat) (a : Fin m) :
    ∃ f : SpiderVertex n m 95 → Nat,
      Graceful (spiderGraph n m 95) (95*n+m) f ∧ f (.leaf a) = 0 := by
  let b : Fin m := ⟨m-1, by have := a.isLt; omega⟩
  let g := fun v => n*95+m-residualLabel n m 95 v
  have hg : Graceful (spiderGraph n m 95) (n*95+m) g :=
    graceful_complement _ _ _ (residual_gracefulness n m 47)
  refine ⟨fun v => g (swapLeafVertex a b v), ?_, ?_⟩
  · simpa [Nat.mul_comm] using graceful_swapLeaf a b g hg
  · simp only [swapLeafVertex, swapIndex_first, g, residualLabel, b]
    have := a.isLt
    omega

end GracefulBoundary.K95Boundary
