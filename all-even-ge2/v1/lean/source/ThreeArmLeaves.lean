import ResidualNamed
namespace GracefulBoundary.CenterLeaves.Full

def graph (k m : Nat) : IndexedGraph (Sum (SpiderVertex 2 m k) (Fin k)) (Sum (SpiderEdge 2 m k) (Fin k)) where
  source := fun e => match e with
    | .inl e => .inl ((spiderGraph 2 m k).source e)
    | .inr d => if d.val=0 then .inl .center else .inr ⟨d.val-1,by omega⟩
  target := fun e => match e with
    | .inl e => .inl ((spiderGraph 2 m k).target e)
    | .inr d => .inr d

def toV (k m : Nat) : SpiderVertex 3 m k → Sum (SpiderVertex 2 m k) (Fin k)
  | .center => .inl .center
  | .leaf j => .inl (.leaf j)
  | .arm i d => if h : i.val=0 then .inr d else .inl (.arm ⟨i.val-1,by omega⟩ d)

def fromV (k m : Nat) : Sum (SpiderVertex 2 m k) (Fin k) → SpiderVertex 3 m k
  | .inr d => .arm ⟨0,by omega⟩ d
  | .inl .center => .center
  | .inl (.leaf j) => .leaf j
  | .inl (.arm i d) => .arm ⟨i.val+1,by omega⟩ d

def toE (k m : Nat) : SpiderEdge 3 m k → Sum (SpiderEdge 2 m k) (Fin k)
  | .leaf j => .inl (.leaf j)
  | .arm i d => if h : i.val=0 then .inr d else .inl (.arm ⟨i.val-1,by omega⟩ d)

def fromE (k m : Nat) : Sum (SpiderEdge 2 m k) (Fin k) → SpiderEdge 3 m k
  | .inr d => .arm ⟨0,by omega⟩ d
  | .inl (.leaf j) => .leaf j
  | .inl (.arm i d) => .arm ⟨i.val+1,by omega⟩ d

theorem vertex_left_inverse (k m : Nat) (v : SpiderVertex 3 m k) : fromV k m (toV k m v)=v := by
  cases v with
  | center => rfl
  | leaf j => rfl
  | arm i d =>
    dsimp only [toV]; split <;> dsimp only [fromV]
    · congr 1; apply Fin.ext; dsimp only; omega
    · congr 1; apply Fin.ext; dsimp only; omega

theorem vertex_right_inverse (k m : Nat) (v : Sum (SpiderVertex 2 m k) (Fin k)) : toV k m (fromV k m v)=v := by
  cases v with
  | inr d => simp only [fromV,toV,dite_true]
  | inl v => cases v with
    | center => rfl
    | leaf j => rfl
    | arm i d =>
      dsimp only [fromV,toV]; rw [dite_eq_right (by omega)]
      congr 3

theorem edge_left_inverse (k m : Nat) (e : SpiderEdge 3 m k) : fromE k m (toE k m e)=e := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    dsimp only [toE]; split <;> dsimp only [fromE]
    · congr 1; apply Fin.ext; dsimp only; omega
    · congr 1; apply Fin.ext; dsimp only; omega

theorem edge_right_inverse (k m : Nat) (e : Sum (SpiderEdge 2 m k) (Fin k)) : toE k m (fromE k m e)=e := by
  cases e with
  | inr d => simp only [fromE,toE,dite_true]
  | inl e => cases e with
    | leaf j => rfl
    | arm i d =>
      dsimp only [fromE,toE]; rw [dite_eq_right (by omega)]
      congr 3

theorem weights (k m : Nat) (f : Sum (SpiderVertex 2 m k) (Fin k) → Nat) (e : SpiderEdge 3 m k) :
    weight (spiderGraph 3 m k) (fun v => f (toV k m v)) e=weight (graph k m) f (toE k m e) := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    by_cases hi : i.val=0
    · by_cases hd : d.val=0 <;> simp only [weight,spiderGraph,toV,toE,graph,hi,hd,dite_true,ite_true,ite_false]
    · by_cases hd : d.val=0 <;> simp only [weight,spiderGraph,toV,toE,graph,hi,hd,dite_false,ite_true,ite_false]

theorem graceful_actual (k m : Nat) (f : Sum (SpiderVertex 2 m k) (Fin k) → Nat) (hf : Graceful (graph k m) (3*k+m) f) :
    Graceful (spiderGraph 3 m k) (3*k+m) (fun v => f (toV k m v)) := by
  constructor
  · exact NearTip.band_transport f 0 (3*k+m) hf.vertices (toV k m) (fromV k m) (vertex_left_inverse k m) (vertex_right_inverse k m)
  · have h := NearTip.band_transport (weight (graph k m) f) 1 (3*k+m) hf.edges (toE k m) (fromE k m) (edge_left_inverse k m) (edge_right_inverse k m)
    have he : weight (spiderGraph 3 m k) (fun v => f (toV k m v))=fun e => weight (graph k m) f (toE k m e) := funext (weights k m f)
    rw [he]; exact h

theorem even_graph (r m : Nat) : LabelOne.graph (spiderGraph 2 m (2*r)) .center r=graph (2*r) m := by
  change IndexedGraph.mk _ _ = IndexedGraph.mk _ _
  congr 1 <;> funext e <;> cases e <;> rfl

theorem odd_graph (r m : Nat) : OddNearTip.graph (spiderGraph 2 m (2*r+1)) .center r=graph (2*r+1) m := by
  change IndexedGraph.mk _ _ = IndexedGraph.mk _ _
  congr 1 <;> funext e <;> cases e <;> rfl

theorem even_first_arm (r m : Nat) (hr : 4≤r) :
    ∃ f : SpiderVertex 3 m (2*r) → Nat, Graceful (spiderGraph 3 m (2*r)) (3*(2*r)+m) f ∧
      f (.arm ⟨0,by omega⟩ ⟨2*r-3,by omega⟩)=0 := by
  obtain ⟨g,hg,hm⟩ := Residual.center_one_two_arm_spider (2*r) m (by omega)
  obtain ⟨f,hf,hz⟩ := LabelOne.even_root_one_attachment (spiderGraph 2 m (2*r)) .center (2*(2*r)+m) r (by omega) g hg hm
  rw [even_graph] at hf
  have size : 2*(2*r)+m+2*r=3*(2*r)+m := by omega
  rw [size] at hf
  exact ⟨fun v => f (toV (2*r) m v),graceful_actual (2*r) m f hf,by simpa only [toV,dite_true] using hz⟩

theorem odd_first_arm (r m : Nat) (hr : 3≤r) :
    ∃ f : SpiderVertex 3 m (2*r+1) → Nat, Graceful (spiderGraph 3 m (2*r+1)) (3*(2*r+1)+m) f ∧
      f (.arm ⟨0,by omega⟩ ⟨2*r+1-3,by omega⟩)=0 := by
  obtain ⟨g,hg,hm⟩ := Residual.center_one_two_arm_spider (2*r+1) m (by omega)
  let Q := 2*(2*r+1)+m
  let h := fun v => Q-g v
  have hh : Graceful (spiderGraph 2 m (2*r+1)) Q h := graceful_complement _ _ g hg
  have root : h .center=Q-1 := by dsimp only [h]; rw [hm]
  obtain ⟨f,hf,hz⟩ := OddNearTip.odd_root_last_attachment (spiderGraph 2 m (2*r+1)) .center Q r hr h hh (by dsimp only [Q]; omega) root
  rw [odd_graph] at hf
  have size : Q+2*r+1=3*(2*r+1)+m := by dsimp only [Q]; omega
  rw [size] at hf
  exact ⟨fun v => f (toV (2*r+1) m v),graceful_actual (2*r+1) m f hf,by simpa only [toV,dite_true] using hz⟩

theorem all_parity_first_arm (k m : Nat) (hk : 7≤k) :
    ∃ f : SpiderVertex 3 m k → Nat, Graceful (spiderGraph 3 m k) (3*k+m) f ∧
      f (.arm ⟨0,by omega⟩ ⟨k-3,by omega⟩)=0 := by
  by_cases he : k%2=0
  · obtain ⟨r,hr,hk'⟩ : ∃r,4≤r ∧ k=2*r := ⟨k/2,by omega,by omega⟩
    subst k; exact even_first_arm r m hr
  · obtain ⟨r,hr,hk'⟩ : ∃r,3≤r ∧ k=2*r+1 := ⟨k/2,by omega,by omega⟩
    subst k; exact odd_first_arm r m hr

/-- Actual named three-arm spider with every short-leaf count and requested arm. -/
theorem all_parity_selected_arm_with_leaves (k m : Nat) (hk : 7≤k) (a : Fin 3) :
    ∃ f : SpiderVertex 3 m k → Nat, Graceful (spiderGraph 3 m k) (3*k+m) f ∧
      f (.arm a ⟨k-3,by omega⟩)=0 := by
  obtain ⟨f,hf,hz⟩ := all_parity_first_arm k m hk
  let z : Fin 3 := ⟨0,by omega⟩
  exact ⟨fun v => f (NearTip.swapVertex a z v),NearTip.graceful_swap a z f hf,by simpa only [NearTip.swapVertex,NearTip.swapIndex_first] using hz⟩

end GracefulBoundary.CenterLeaves.Full
