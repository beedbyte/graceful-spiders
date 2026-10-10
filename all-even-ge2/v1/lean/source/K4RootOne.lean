import K4Partial
import AllEvenGe6

namespace GracefulBoundary.K4RootOne

/-- The literal center-one, maximum-at-depth-one k=4 construction, before
    adjoining original hub leaves. Arm zero is the selected arm. -/
def base (n : Nat) : SpiderVertex n 0 4 → Nat
  | .center => 1
  | .leaf j => Fin.elim0 j
  | .arm i d =>
    if i.val = 0 then
      if d.val = 0 then 4*n
      else if d.val = 1 then 0
      else if d.val = 2 then 4*n-2
      else 3
    else
      if d.val = 0 then 4*(n-i.val)+1
      else if d.val = 1 then 4*i.val
      else if d.val = 2 then 4*(n-i.val)-2
      else 4*i.val+3

theorem base_center (n : Nat) : base n (.center : SpiderVertex n 0 4)=1 := rfl

theorem base_max (n : Nat) (hn : 0<n) :
    base n (.arm ⟨0,hn⟩ ⟨0,by decide⟩)=4*n := by simp [base]

theorem base_zero (n : Nat) (hn : 0<n) :
    base n (.arm ⟨0,hn⟩ ⟨1,by decide⟩)=0 := by simp [base]

/-- The exact remaining base obligation. This definition is not an axiom. -/
def BaseGracefulness : Prop :=
  ∀ n, 1 ≤ n → Graceful (spiderGraph n 0 4) (4*n) (base n)

/-- The established maximum-leaf theorem transfers the exact base contract
    to every original-leaf count and every selected arm. -/
theorem depth_one_of_base (hbase : BaseGracefulness) (n m : Nat)
    (hn : 2 ≤ n) (a : Fin n) :
    ∃ f : SpiderVertex n m 4 → Nat,
      Graceful (spiderGraph n m 4) (n*4+m) f ∧
      f (.arm a ⟨0,by decide⟩)=0 := by
  let z : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let g : SpiderVertex n 0 4 → Nat := fun v => base n (NearTip.swapVertex b z v)
  have hg : Graceful (spiderGraph n 0 4) (n*4) g := by
    simpa only [show 4*n=n*4 by omega] using
      NearTip.graceful_swap b z (base n) (hbase n (by omega))
  have hr : g .center=1 := by simp [g,NearTip.swapVertex,base]
  have hm : g (.arm b ⟨0,by decide⟩)=n*4 := by
    simpa only [g,NearTip.swapVertex,NearTip.swapIndex_first,
      show 4*n=n*4 by omega] using base_max n (by omega)
  have hz : g (.arm b ⟨1,by decide⟩)=0 := by
    simpa only [g,NearTip.swapVertex,NearTip.swapIndex_first] using
      base_zero n (by omega)
  have hq : 2≤n*4 := by omega
  have hleaf := FixedEven.maximum_leaf_extension (spiderGraph n 0 4)
    (n*4) m g hg .center (.arm b ⟨0,by decide⟩)
    (.arm b ⟨1,by decide⟩) (.arm b ⟨0,by decide⟩)
    (.arm b ⟨1,by decide⟩)
    (EvenUniform.actual_maximum_anchor n 4 hn (by decide)) hr hm hz hq
  let u : SpiderVertex n m 4 → Nat :=
    fun v => CenterLeaves.insertLabel g (n*4) m (FixedEven.Leaf.toV n m 4 v)
  have hu : Graceful (spiderGraph n m 4) (n*4+m) u :=
    FixedEven.Leaf.graceful_actual n m 4 (n*4+m) _ hleaf.1
  have hum : u (.arm b ⟨0,by decide⟩)=n*4+m := by
    dsimp only [u,FixedEven.Leaf.toV,CenterLeaves.insertLabel]
    rw [hm,ite_eq_left (by omega)]
  let t : SpiderVertex n m 4 → Nat := fun v => u (NearTip.swapVertex a b v)
  have ht : Graceful (spiderGraph n m 4) (n*4+m) t :=
    NearTip.graceful_swap a b u hu
  have htm : t (.arm a ⟨0,by decide⟩)=n*4+m := by
    simpa only [t,NearTip.swapVertex,NearTip.swapIndex_first] using hum
  exact ⟨complementLabel (n*4+m) t,
    whole_graph_graceful_complement _ _ t ht,
    complement_maximum_zero _ t _ htm⟩

end GracefulBoundary.K4RootOne

#print axioms GracefulBoundary.K4RootOne.depth_one_of_base
