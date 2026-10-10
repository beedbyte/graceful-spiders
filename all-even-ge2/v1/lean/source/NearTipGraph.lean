import MidpointPath
import OddAttachment

namespace GracefulBoundary.NearTip

def graph (k : Nat) : IndexedGraph (Sum (Fin (2*k+1)) (Fin k)) (Sum (Fin (2*k)) (Fin k)) where
  source := fun e => match e with
    | .inl e => .inl ⟨e.val,by omega⟩
    | .inr d => if d.val=0 then .inl ⟨k,by omega⟩ else .inr ⟨d.val-1,by omega⟩
  target := fun e => match e with
    | .inl e => .inl ⟨e.val+1,by omega⟩
    | .inr d => .inr d

def toV (k : Nat) : SpiderVertex 3 0 k → Sum (Fin (2*k+1)) (Fin k)
  | .center => .inl ⟨k,by omega⟩
  | .leaf j => nomatch j
  | .arm i d => if i.val=0 then .inr d else if i.val=1 then .inl ⟨k-1-d.val,by omega⟩ else .inl ⟨k+1+d.val,by omega⟩

def fromV (k : Nat) : Sum (Fin (2*k+1)) (Fin k) → SpiderVertex 3 0 k
  | .inr d => .arm ⟨0,by omega⟩ d
  | .inl v => if h0 : v.val=k then .center else if h : v.val<k then .arm ⟨1,by omega⟩ ⟨k-1-v.val,by omega⟩ else .arm ⟨2,by omega⟩ ⟨v.val-k-1,by have := v.isLt; have := h0; omega⟩

def toE (k : Nat) : SpiderEdge 3 0 k → Sum (Fin (2*k)) (Fin k)
  | .leaf j => nomatch j
  | .arm i d => if i.val=0 then .inr d else if i.val=1 then .inl ⟨k-1-d.val,by omega⟩ else .inl ⟨k+d.val,by omega⟩

def fromE (k : Nat) : Sum (Fin (2*k)) (Fin k) → SpiderEdge 3 0 k
  | .inr d => .arm ⟨0,by omega⟩ d
  | .inl e => if h : e.val<k then .arm ⟨1,by omega⟩ ⟨k-1-e.val,by omega⟩ else .arm ⟨2,by omega⟩ ⟨e.val-k,by omega⟩

theorem vertex_left_inverse (k : Nat) (v : SpiderVertex 3 0 k) : fromV k (toV k v)=v := by
  cases v with
  | center => simp only [toV,fromV,dite_true]
  | leaf j => exact Fin.elim0 j
  | arm i d =>
    dsimp only [toV]
    by_cases h0 : i.val=0
    · rw [ite_eq_left h0]; dsimp only [fromV]; congr 1; apply Fin.ext; dsimp only; omega
    · rw [ite_eq_right h0]
      by_cases h1 : i.val=1
      · rw [ite_eq_left h1]; dsimp only [fromV]
        rw [dite_eq_right (by omega),dite_eq_left (by omega)]
        congr 1 <;> apply Fin.ext <;> dsimp only <;> omega
      · rw [ite_eq_right h1]; dsimp only [fromV]
        rw [dite_eq_right (by omega),dite_eq_right (by omega)]
        congr 1 <;> apply Fin.ext <;> dsimp only <;> omega

theorem vertex_right_inverse (k : Nat) (v : Sum (Fin (2*k+1)) (Fin k)) : toV k (fromV k v)=v := by
  cases v with
  | inr d => simp only [fromV,toV,ite_true]
  | inl v =>
    dsimp only [fromV]
    split
    · dsimp only [toV]; congr 1; apply Fin.ext; dsimp only; omega
    · split
      · simp only [toV,show (1:Nat)≠0 by omega,ite_false,ite_true]
        congr 1; apply Fin.ext; dsimp only; omega
      · simp only [toV,show (2:Nat)≠0 by omega,show (2:Nat)≠1 by omega,ite_false]
        congr 1; apply Fin.ext; dsimp only; omega

theorem edge_left_inverse (k : Nat) (e : SpiderEdge 3 0 k) : fromE k (toE k e)=e := by
  cases e with
  | leaf j => exact Fin.elim0 j
  | arm i d =>
    dsimp only [toE]
    by_cases h0 : i.val=0
    · rw [ite_eq_left h0]; dsimp only [fromE]; congr 1; apply Fin.ext; dsimp only; omega
    · rw [ite_eq_right h0]
      by_cases h1 : i.val=1
      · rw [ite_eq_left h1]; dsimp only [fromE]; rw [dite_eq_left (by omega)]
        congr 1 <;> apply Fin.ext <;> dsimp only <;> omega
      · rw [ite_eq_right h1]; dsimp only [fromE]; rw [dite_eq_right (by omega)]
        congr 1 <;> apply Fin.ext <;> dsimp only <;> omega

theorem edge_right_inverse (k : Nat) (e : Sum (Fin (2*k)) (Fin k)) : toE k (fromE k e)=e := by
  cases e with
  | inr d => simp only [fromE,toE,ite_true]
  | inl e =>
    dsimp only [fromE]
    split
    · simp only [toE,show (1:Nat)≠0 by omega,ite_false,ite_true]
      congr 1; apply Fin.ext; dsimp only; omega
    · simp only [toE,show (2:Nat)≠0 by omega,show (2:Nat)≠1 by omega,ite_false]
      congr 1; apply Fin.ext; dsimp only; omega

theorem weights (k : Nat) (f : Sum (Fin (2*k+1)) (Fin k) → Nat) (e : SpiderEdge 3 0 k) :
    weight (spiderGraph 3 0 k) (fun v => f (toV k v)) e=weight (graph k) f (toE k e) := by
  cases e with
  | leaf j => exact Fin.elim0 j
  | arm i d =>
    by_cases h0 : i.val=0
    · by_cases hd : d.val=0 <;> simp only [weight,spiderGraph,toV,toE,graph,h0,hd,ite_true,ite_false]
    · by_cases h1 : i.val=1
      · by_cases hd : d.val=0
        · simp only [weight,spiderGraph,toV,toE,graph,h1,hd,ite_true,ite_false,show (1:Nat)≠0 by omega]
          have he : (⟨k-1-0+1,by omega⟩ : Fin (2*k+1))=⟨k,by omega⟩ := by apply Fin.ext; dsimp only; omega
          rw [he,distance_comm]
        · simp only [weight,spiderGraph,toV,toE,graph,h1,hd,ite_true,ite_false,show (1:Nat)≠0 by omega]
          have he : (⟨k-1-(d.val-1),by omega⟩ : Fin (2*k+1))=⟨k-1-d.val+1,by omega⟩ := by apply Fin.ext; dsimp only; omega
          rw [he,distance_comm]
      · by_cases hd : d.val=0
        · simp only [weight,spiderGraph,toV,toE,graph,h0,h1,hd,ite_true,ite_false]
          rfl
        · simp only [weight,spiderGraph,toV,toE,graph,h0,h1,hd,ite_false]
          have he : (⟨k+1+(d.val-1),by omega⟩ : Fin (2*k+1))=⟨k+d.val,by omega⟩ := by apply Fin.ext; dsimp only; omega
          rw [he]
          congr 3; apply Fin.ext; dsimp only; omega

theorem band_transport {V W : Type} (f : V → Nat) (lo hi : Nat) (hf : BandBijection f lo hi)
    (v : W → V) (vi : V → W) (hl : ∀x,vi (v x)=x) (hr : ∀x,v (vi x)=x) : BandBijection (fun x => f (v x)) lo hi := by
  constructor
  · intro x; exact hf.bounds (v x)
  · intro x y he; have h := congrArg vi (hf.injective _ _ he); simpa only [hl] using h
  · intro x hx ht; obtain ⟨a,ha⟩ := hf.onto x hx ht; exact ⟨vi a,by rw [hr,ha]⟩

theorem graceful_actual (k : Nat) (f : Sum (Fin (2*k+1)) (Fin k) → Nat) (hf : Graceful (graph k) (3*k) f) :
    Graceful (spiderGraph 3 0 k) (3*k) (fun v => f (toV k v)) := by
  constructor
  · exact band_transport f 0 (3*k) hf.vertices (toV k) (fromV k) (vertex_left_inverse k) (vertex_right_inverse k)
  · have h := band_transport (weight (graph k) f) 1 (3*k) hf.edges (toE k) (fromE k) (edge_left_inverse k) (edge_right_inverse k)
    have he : weight (spiderGraph 3 0 k) (fun v => f (toV k v))=fun e => weight (graph k) f (toE k e) := funext (weights k f)
    rw [he]; exact h

end GracefulBoundary.NearTip
