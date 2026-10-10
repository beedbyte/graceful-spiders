import Certificates
namespace GracefulBoundary

/-- An explicitly OPEN obligation, not an axiom or a proved theorem. -/
def RecurrencePreservesInvariant : Prop :=
  ∀ (s : Nat) (c : List Nat), CoreInvariant s c → CoreInvariant (s+2) (extend s c)

/-- Conditional assembly only. It does not discharge its `step` argument. -/
theorem uniform_cores_if_recurrence (step : RecurrencePreservesInvariant) :
    ∀ s, 2 ≤ s → ∃ c, CoreInvariant s c := by
  apply induction_from_two_seeds (fun s => ∃ c, CoreInvariant s c)
  · exact ⟨seed2, seed2_valid⟩
  · exact ⟨seed3, seed3_valid⟩
  · intro s _ hs
    obtain ⟨c,hc⟩ := hs
    exact ⟨extend s c, step s c hc⟩

/-- This structural part of the recurrence is universal and discharged. -/
theorem extend_length (s : Nat) (c : List Nat) (hs : 2 ≤ s) (hc : c.length=6*s) :
    (extend s c).length = 6*(s+2) := by
  simp only [extend, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_take, List.length_drop, hc]
  omega

/-- The shell's core contract has no H4/L1 neighbour requirement. -/
def BoundaryCore (p : Nat) (c : List Nat) : Prop :=
  4 ≤ p ∧ c.length=2*p ∧ (highs c).Perm (List.range p) ∧
  (lows c).Perm (List.range p) ∧ (edgeSums c).Perm (List.range (2*p-1)) ∧
  c[0]?=some 3 ∧ c[2*p-1]?=some (p-4)

def GenericPathCertificate (p : Nat) (c : List Nat) : Prop :=
  c.length=4*p+7 ∧ c.Perm (List.range (4*p+7)) ∧
  (edgeDiffs c).Perm (List.range' 1 (4*p+6)) ∧
  crosses (2*p+2) c ∧ c[2*p+3]?=some (2*p+2)

/-- Open uniform structural shell obligation for every qualifying core. -/
def BoundaryShellBridge : Prop :=
  ∀ p c, BoundaryCore p c → GenericPathCertificate p (completePath p c)

theorem core_boundary_contract (s : Nat) (c : List Nat) (h : CoreInvariant s c) :
    BoundaryCore (3*s) c := by
  rcases h with ⟨hs, hlen, hh, hl, he, hf, ht, _⟩
  refine ⟨by omega, ?_, hh, hl, ?_, hf, ?_⟩
  · simpa [show 2*(3*s)=6*s by omega] using hlen
  · simpa [show 2*(3*s)=6*s by omega] using he
  · simpa [show 2*(3*s)=6*s by omega] using ht
/-- An explicitly OPEN core-to-complete-path structural theorem. -/
def CoreToPathBridge : Prop :=
  ∀ (s : Nat) (c : List Nat), CoreInvariant s c → PathCertificate s (completePath (3*s) c)

/-- Indexed actual spider graph, including center and all short leaves. -/
inductive SpiderVertex (n m k : Nat) where
  | center
  | arm (index : Fin n) (depthMinusOne : Fin k)
  | leaf (index : Fin m)
  deriving DecidableEq

inductive SpiderEdge (n m k : Nat) where
  | arm (index : Fin n) (depthMinusOne : Fin k)
  | leaf (index : Fin m)
  deriving DecidableEq

def spiderGraph (n m k : Nat) : IndexedGraph (SpiderVertex n m k) (SpiderEdge n m k) where
  source := fun e => match e with
    | .leaf _ => .center
    | .arm i d => if d.val=0 then .center else .arm i ⟨d.val-1, by omega⟩
  target := fun e => match e with
    | .leaf j => .leaf j
    | .arm i d => .arm i d

def residualLabel (h m k : Nat) : SpiderVertex h m k → Nat
  | .center => 0
  | .leaf j => h*k+j.val+1
  | .arm i d => if d.val%2=0 then (h-i.val)*k-d.val/2 else i.val*k+(d.val+1)/2

/-- This is a formal statement of the inherited residual formula's remaining
    proof obligation, including h=0,m=0. It is not an axiom. -/
def ResidualGracefulness : Prop :=
  ∀ h m r, Graceful (spiderGraph h m (2*r+1)) (h*(2*r+1)+m) (residualLabel h m (2*r+1))

/-- Shared-center label needed by the already proved general graft theorem. -/
theorem residual_center_zero (h m k : Nat) :
    residualLabel h m k .center = 0 := rfl

/-- Arithmetic binding of the boundary path and the full spider size. -/
theorem spider_size_accounting (s n m : Nat) (hn : 2 ≤ n) :
    12*s+6 + ((n-2)*(6*s+3)+m) = n*(6*s+3)+m := by
  have h : n=(n-2)+2 := by omega
  have hmul := congrArg (fun x => x*(6*s+3)) h
  simp only [Nat.add_mul] at hmul
  omega

end GracefulBoundary


