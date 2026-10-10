import ThreeArmTheorem
namespace GracefulBoundary.NearTip
def swapIndex {n : Nat} (a b i : Fin n) : Fin n :=
  if i=a then b else if i=b then a else i

theorem swapIndex_first {n : Nat} (a b : Fin n) : swapIndex a b a=b := by
  simp only [swapIndex,ite_true]

theorem swapIndex_second {n : Nat} (a b : Fin n) : swapIndex a b b=a := by
  by_cases he : b=a
  · subst b; exact swapIndex_first a a
  · simp only [swapIndex,he,ite_false,ite_true]

theorem swapIndex_involution {n : Nat} (a b i : Fin n) : swapIndex a b (swapIndex a b i)=i := by
  by_cases ha : i=a
  · subst i; rw [swapIndex_first,swapIndex_second]
  · by_cases hb : i=b
    · subst i; rw [swapIndex_second,swapIndex_first]
    · simp only [swapIndex,ha,hb,ite_false]

def swapVertex {n m k : Nat} (a b : Fin n) : SpiderVertex n m k → SpiderVertex n m k
  | .center => .center
  | .leaf j => .leaf j
  | .arm i d => .arm (swapIndex a b i) d

def swapEdge {n m k : Nat} (a b : Fin n) : SpiderEdge n m k → SpiderEdge n m k
  | .leaf j => .leaf j
  | .arm i d => .arm (swapIndex a b i) d

theorem swapVertex_involution {n m k : Nat} (a b : Fin n) (v : SpiderVertex n m k) :
    swapVertex a b (swapVertex a b v)=v := by
  cases v <;> simp only [swapVertex,swapIndex_involution]

theorem swapEdge_involution {n m k : Nat} (a b : Fin n) (e : SpiderEdge n m k) :
    swapEdge a b (swapEdge a b e)=e := by
  cases e <;> simp only [swapEdge,swapIndex_involution]

theorem swap_weights {n m k : Nat} (a b : Fin n) (f : SpiderVertex n m k → Nat)
    (e : SpiderEdge n m k) :
    weight (spiderGraph n m k) (fun v => f (swapVertex a b v)) e =
      weight (spiderGraph n m k) f (swapEdge a b e) := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    by_cases hd : d.val=0 <;> simp only [weight,spiderGraph,swapEdge,swapVertex,hd,ite_true,ite_false]

theorem graceful_swap {n m k M : Nat} (a b : Fin n) (f : SpiderVertex n m k → Nat)
    (hf : Graceful (spiderGraph n m k) M f) :
    Graceful (spiderGraph n m k) M (fun v => f (swapVertex a b v)) := by
  constructor
  · exact band_transport f 0 M hf.vertices (swapVertex a b) (swapVertex a b) (swapVertex_involution a b) (swapVertex_involution a b)
  · have hb := band_transport (weight (spiderGraph n m k) f) 1 M hf.edges (swapEdge a b) (swapEdge a b) (swapEdge_involution a b) (swapEdge_involution a b)
    have he : weight (spiderGraph n m k) (fun v => f (swapVertex a b v))=fun e => weight (spiderGraph n m k) f (swapEdge a b e) := funext (swap_weights a b f)
    rw [he]; exact hb

/-- Actual three-arm spider, any requested arm, zero at one-based depth k-2. -/
theorem all_parity_selected_arm (k : Nat) (hk : 7≤k) (a : Fin 3) :
    ∃ f : SpiderVertex 3 0 k → Nat,
      Graceful (spiderGraph 3 0 k) (3*k) f ∧ f (.arm a ⟨k-3,by omega⟩)=0 := by
  obtain ⟨f,hf,hz⟩ := all_parity_first_arm k hk
  let z : Fin 3 := ⟨0,by omega⟩
  exact ⟨fun v => f (swapVertex a z v),graceful_swap a z f hf,by simpa only [swapVertex,swapIndex_first] using hz⟩

end GracefulBoundary.NearTip
