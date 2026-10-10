import Identification
namespace GracefulBoundary

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
    Graceful (spiderGraph n m k) M (fun v => f (swapVertex a b v)) :=
  graceful_transport (spiderGraph n m k) (spiderGraph n m k) M f hf
    (swapVertex a b) (swapVertex a b) (swapEdge a b) (swapEdge a b)
    (swapVertex_involution a b) (swapVertex_involution a b)
    (swapEdge_involution a b) (swapEdge_involution a b) (swap_weights a b f)

/-- One labeling on any requested arm has zero at depth 4s and the largest
    label at depth 4s+1. Depths are one-based distances from the center. -/
theorem uniform_selected_arm_anchors (s n m : Nat) (hs : 2 ≤ s) (hn : 2 ≤ n) (a : Fin n) :
    ∃ f : SpiderVertex n m (6*s+3) → Nat,
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) f ∧
      f (.arm a ⟨4*s-1,by omega⟩)=0 ∧
      f (.arm a ⟨4*s,by omega⟩)=n*(6*s+3)+m := by
  obtain ⟨h,rfl⟩ : ∃ h,n=h+2 := ⟨n-2,by omega⟩
  obtain ⟨f,hf,hzero,hmax⟩ := uniform_first_arm_spiders s h m hs
  let z : Fin (h+2) := ⟨0,by omega⟩
  refine ⟨fun v => f (swapVertex a z v),graceful_swap a z f hf,?_,?_⟩
  · simpa only [swapVertex,swapIndex_first] using hzero
  · simpa only [swapVertex,swapIndex_first] using hmax

/-- Unconditional first-pair prescribed-zero theorem on the actual indexed
    spider, for every number of short leaves and every requested long arm. -/
theorem first_pair_prescribed_zero (s n m : Nat) (hs : 2 ≤ s) (hn : 2 ≤ n) (a : Fin n) :
    (∃ f : SpiderVertex n m (6*s+3) → Nat,
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) f ∧
      f (.arm a ⟨4*s-1,by omega⟩)=0) ∧
    (∃ g : SpiderVertex n m (6*s+3) → Nat,
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) g ∧
      g (.arm a ⟨4*s,by omega⟩)=0) := by
  obtain ⟨f,hf,hzero,hmax⟩ := uniform_selected_arm_anchors s n m hs hn a
  constructor
  · exact ⟨f,hf,hzero⟩
  · refine ⟨fun v => n*(6*s+3)+m-f v,graceful_complement _ _ f hf,?_⟩
    simp only [hmax,Nat.sub_self]

/-- Same result with an explicitly supplied permitted one-based depth. -/
theorem first_pair_at_depth (s n m d : Nat) (hs : 2 ≤ s) (hn : 2 ≤ n)
    (hd : d=4*s ∨ d=4*s+1) (a : Fin n) :
    ∃ (hlt : d-1 < 6*s+3) (f : SpiderVertex n m (6*s+3) → Nat),
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 := by
  have hh := first_pair_prescribed_zero s n m hs hn a
  cases hd with
  | inl hd => subst d; exact ⟨by omega,hh.1⟩
  | inr hd =>
    subst d
    have he : 4*s+1-1=4*s := by omega
    simpa only [he] using (show ∃ (hlt : 4*s < 6*s+3) (f : SpiderVertex n m (6*s+3) → Nat),
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) f ∧ f (.arm a ⟨4*s,hlt⟩)=0 from ⟨by omega,hh.2⟩)

end GracefulBoundary
