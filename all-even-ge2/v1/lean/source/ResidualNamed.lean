import PathLeaves
namespace GracefulBoundary.CenterLeaves.Residual

def toV (k m : Nat) : SpiderVertex 2 m k → Sum (Fin (2*k+1)) (Fin m)
  | .center => .inl ⟨k,by omega⟩
  | .leaf j => .inr j
  | .arm i d => if i.val=0 then .inl ⟨k-1-d.val,by omega⟩ else .inl ⟨k+1+d.val,by omega⟩

def fromV (k m : Nat) : Sum (Fin (2*k+1)) (Fin m) → SpiderVertex 2 m k
  | .inr j => .leaf j
  | .inl v => if h0 : v.val=k then .center else if h : v.val<k then .arm ⟨0,by omega⟩ ⟨k-1-v.val,by omega⟩ else .arm ⟨1,by omega⟩ ⟨v.val-k-1,by have := v.isLt; have := h0; omega⟩

def toE (k m : Nat) : SpiderEdge 2 m k → Sum (Fin (2*k)) (Fin m)
  | .leaf j => .inr j
  | .arm i d => if i.val=0 then .inl ⟨k-1-d.val,by omega⟩ else .inl ⟨k+d.val,by omega⟩

def fromE (k m : Nat) : Sum (Fin (2*k)) (Fin m) → SpiderEdge 2 m k
  | .inr j => .leaf j
  | .inl e => if h : e.val<k then .arm ⟨0,by omega⟩ ⟨k-1-e.val,by omega⟩ else .arm ⟨1,by omega⟩ ⟨e.val-k,by omega⟩

theorem vertex_left_inverse (k m : Nat) (v : SpiderVertex 2 m k) : fromV k m (toV k m v)=v := by
  cases v with
  | center => simp only [toV,fromV,dite_true]
  | leaf j => rfl
  | arm i d =>
    dsimp only [toV]
    by_cases h0 : i.val=0
    · rw [ite_eq_left h0]; dsimp only [fromV]
      rw [dite_eq_right (by omega),dite_eq_left (by omega)]
      congr 1 <;> apply Fin.ext <;> dsimp only <;> omega
    · rw [ite_eq_right h0]; dsimp only [fromV]
      rw [dite_eq_right (by omega),dite_eq_right (by omega)]
      congr 1 <;> apply Fin.ext <;> dsimp only <;> omega

theorem vertex_right_inverse (k m : Nat) (v : Sum (Fin (2*k+1)) (Fin m)) : toV k m (fromV k m v)=v := by
  cases v with
  | inr j => rfl
  | inl v =>
    dsimp only [fromV]; split
    · dsimp only [toV]; congr 1; apply Fin.ext; dsimp only; omega
    · split
      · simp only [toV,ite_true]; congr 1; apply Fin.ext; dsimp only; omega
      · simp only [toV,show (1:Nat)≠0 by omega,ite_false]; congr 1; apply Fin.ext; dsimp only; omega

theorem edge_left_inverse (k m : Nat) (e : SpiderEdge 2 m k) : fromE k m (toE k m e)=e := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    dsimp only [toE]
    by_cases h0 : i.val=0
    · rw [ite_eq_left h0]; dsimp only [fromE]; rw [dite_eq_left (by omega)]
      congr 1 <;> apply Fin.ext <;> dsimp only <;> omega
    · rw [ite_eq_right h0]; dsimp only [fromE]; rw [dite_eq_right (by omega)]
      congr 1 <;> apply Fin.ext <;> dsimp only <;> omega

theorem edge_right_inverse (k m : Nat) (e : Sum (Fin (2*k)) (Fin m)) : toE k m (fromE k m e)=e := by
  cases e with
  | inr j => rfl
  | inl e =>
    dsimp only [fromE]; split
    · simp only [toE,ite_true]; congr 1; apply Fin.ext; dsimp only; omega
    · simp only [toE,show (1:Nat)≠0 by omega,ite_false]; congr 1; apply Fin.ext; dsimp only; omega

theorem weights (k m : Nat) (f : Sum (Fin (2*k+1)) (Fin m) → Nat) (e : SpiderEdge 2 m k) :
    weight (spiderGraph 2 m k) (fun v => f (toV k m v)) e=weight (CenterLeaves.graph k m) f (toE k m e) := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    by_cases h0 : i.val=0
    · by_cases hd : d.val=0
      · simp only [weight,spiderGraph,toV,toE,CenterLeaves.graph,h0,hd,ite_true]
        have he : (⟨k-1-0+1,by omega⟩ : Fin (2*k+1))=⟨k,by omega⟩ := by apply Fin.ext; dsimp only; omega
        rw [he,distance_comm]
      · simp only [weight,spiderGraph,toV,toE,CenterLeaves.graph,h0,hd,ite_true,ite_false]
        have he : (⟨k-1-(d.val-1),by omega⟩ : Fin (2*k+1))=⟨k-1-d.val+1,by omega⟩ := by apply Fin.ext; dsimp only; omega
        rw [he,distance_comm]
    · by_cases hd : d.val=0
      · simp only [weight,spiderGraph,toV,toE,CenterLeaves.graph,h0,hd,ite_true,ite_false]; rfl
      · simp only [weight,spiderGraph,toV,toE,CenterLeaves.graph,h0,hd,ite_false]
        have he : (⟨k+1+(d.val-1),by omega⟩ : Fin (2*k+1))=⟨k+d.val,by omega⟩ := by apply Fin.ext; dsimp only; omega
        rw [he]; congr 3; apply Fin.ext; dsimp only; omega

theorem graceful_actual (k m : Nat) (f : Sum (Fin (2*k+1)) (Fin m) → Nat) (hf : Graceful (CenterLeaves.graph k m) (2*k+m) f) :
    Graceful (spiderGraph 2 m k) (2*k+m) (fun v => f (toV k m v)) := by
  constructor
  · exact NearTip.band_transport f 0 (2*k+m) hf.vertices (toV k m) (fromV k m) (vertex_left_inverse k m) (vertex_right_inverse k m)
  · have h := NearTip.band_transport (weight (CenterLeaves.graph k m) f) 1 (2*k+m) hf.edges (toE k m) (fromE k m) (edge_left_inverse k m) (edge_right_inverse k m)
    have he : weight (spiderGraph 2 m k) (fun v => f (toV k m v))=fun e => weight (CenterLeaves.graph k m) f (toE k m e) := funext (weights k m f)
    rw [he]; exact h

/-- Universal path-anchor maximum lift, with output on the actual named two-arm spider. -/
theorem pinned_path_to_named_leaf_extension (k m : Nat) (hk : 2≤k) (g : Fin (2*k+1) → Nat)
    (hg : Graceful (pathGraph (2*k)) (2*k) g)
    (hroot : g ⟨k,by omega⟩=1) (hmax : g ⟨k+1,by omega⟩=2*k) (hzero : g ⟨k+2,by omega⟩=0) :
    ∃ f : SpiderVertex 2 m k → Nat, Graceful (spiderGraph 2 m k) (2*k+m) f ∧
      f .center=1 ∧ f (.arm ⟨1,by omega⟩ ⟨0,by omega⟩)=2*k+m ∧
      f (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)=0 ∧ ∀j:Fin m,f (.leaf j)=2*k+j.val := by
  let f := insertLabel g (2*k) m
  have hf := (pinned_path_leaf_extension k m hk g hg hroot hmax hzero).1
  refine ⟨fun v => f (toV k m v),graceful_actual k m f hf,?_,?_,?_,?_⟩
  · exact (pinned_path_leaf_extension k m hk g hg hroot hmax hzero).2
  · simp only [toV,show (1:Nat)≠0 by omega,ite_false,f,insertLabel,hmax,Nat.le_refl,ite_true]
  · simp only [toV,show (1:Nat)≠0 by omega,ite_false,f,insertLabel,hzero,show ¬2*k≤0 by omega,ite_false]
  · intro j; rfl

theorem center_one_two_arm_spider (k m : Nat) (hk : 7≤k) :
    ∃ f : SpiderVertex 2 m k → Nat, Graceful (spiderGraph 2 m k) (2*k+m) f ∧ f .center=1 := by
  obtain ⟨g,hg,hr,hm,hz⟩ := midpoint_pinned_graceful_path k hk
  obtain ⟨f,hf,hc,_⟩ := pinned_path_to_named_leaf_extension k m (by omega) g hg hr hm hz
  exact ⟨f,hf,hc⟩

end GracefulBoundary.CenterLeaves.Residual
