import StepEight
namespace GracefulBoundary.FixedEven.Append

def toV (n m k : Nat) : SpiderVertex (n+1) m k → Sum (SpiderVertex n m k) (Fin k)
  | .center => .inl .center
  | .leaf j => .inl (.leaf j)
  | .arm i d => if hi : i.val<n then .inl (.arm ⟨i.val,hi⟩ d) else .inr d

def fromV (n m k : Nat) : Sum (SpiderVertex n m k) (Fin k) → SpiderVertex (n+1) m k
  | .inr d => .arm ⟨n,by omega⟩ d
  | .inl .center => .center
  | .inl (.leaf j) => .leaf j
  | .inl (.arm i d) => .arm ⟨i.val,by omega⟩ d

def toE (n m k : Nat) : SpiderEdge (n+1) m k → Sum (SpiderEdge n m k) (Fin k)
  | .leaf j => .inl (.leaf j)
  | .arm i d => if hi : i.val<n then .inl (.arm ⟨i.val,hi⟩ d) else .inr d

def fromE (n m k : Nat) : Sum (SpiderEdge n m k) (Fin k) → SpiderEdge (n+1) m k
  | .inr d => .arm ⟨n,by omega⟩ d
  | .inl (.leaf j) => .leaf j
  | .inl (.arm i d) => .arm ⟨i.val,by omega⟩ d

theorem vertex_left_inverse (n m k : Nat) (v : SpiderVertex (n+1) m k) : fromV n m k (toV n m k v)=v := by
  cases v with
  | center => rfl
  | leaf j => rfl
  | arm i d =>
    dsimp only [toV]; split <;> dsimp only [fromV]
    congr 1; apply Fin.ext; dsimp only; omega

theorem vertex_right_inverse (n m k : Nat) (v : Sum (SpiderVertex n m k) (Fin k)) : toV n m k (fromV n m k v)=v := by
  cases v with
  | inr d => simp only [fromV,toV,Nat.lt_irrefl,dite_false]
  | inl v => cases v with
    | center => rfl
    | leaf j => rfl
    | arm i d => dsimp only [fromV,toV]; rw [dite_eq_left i.isLt]

theorem edge_left_inverse (n m k : Nat) (e : SpiderEdge (n+1) m k) : fromE n m k (toE n m k e)=e := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    dsimp only [toE]; split <;> dsimp only [fromE]
    congr 1; apply Fin.ext; dsimp only; omega

theorem edge_right_inverse (n m k : Nat) (e : Sum (SpiderEdge n m k) (Fin k)) : toE n m k (fromE n m k e)=e := by
  cases e with
  | inr d => simp only [fromE,toE,Nat.lt_irrefl,dite_false]
  | inl e => cases e with
    | leaf j => rfl
    | arm i d => dsimp only [fromE,toE]; rw [dite_eq_left i.isLt]

theorem source_eq (n m k : Nat) (e : SpiderEdge (n+1) m k) :
    toV n m k ((spiderGraph (n+1) m k).source e)=
      (FixedEven.graph (spiderGraph n m k) .center k).source (toE n m k e) := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    by_cases hi : i.val<n <;> by_cases hd : d.val=0 <;>
      simp only [spiderGraph,toV,toE,FixedEven.graph,hi,hd,dite_true,dite_false,ite_true,ite_false]

theorem target_eq (n m k : Nat) (e : SpiderEdge (n+1) m k) :
    toV n m k ((spiderGraph (n+1) m k).target e)=
      (FixedEven.graph (spiderGraph n m k) .center k).target (toE n m k e) := by
  cases e with
  | leaf j => rfl
  | arm i d => by_cases hi : i.val<n <;> simp only [spiderGraph,toV,toE,FixedEven.graph,hi,dite_true,dite_false]

theorem weights (n m k : Nat) (f : Sum (SpiderVertex n m k) (Fin k) → Nat) (e : SpiderEdge (n+1) m k) :
    weight (spiderGraph (n+1) m k) (fun v => f (toV n m k v)) e=
      weight (FixedEven.graph (spiderGraph n m k) .center k) f (toE n m k e) := by
  dsimp only [weight]; rw [source_eq,target_eq]

theorem graceful_actual (n m k q : Nat) (f : Sum (SpiderVertex n m k) (Fin k) → Nat)
    (hf : Graceful (FixedEven.graph (spiderGraph n m k) .center k) q f) :
    Graceful (spiderGraph (n+1) m k) q (fun v => f (toV n m k v)) := by
  constructor
  · exact NearTip.band_transport f 0 q hf.vertices (toV n m k) (fromV n m k) (vertex_left_inverse n m k) (vertex_right_inverse n m k)
  · have h := NearTip.band_transport (weight (FixedEven.graph (spiderGraph n m k) .center k) f) 1 q hf.edges (toE n m k) (fromE n m k) (edge_left_inverse n m k) (edge_right_inverse n m k)
    have he := funext (weights n m k f)
    rw [he]; exact h

end GracefulBoundary.FixedEven.Append
