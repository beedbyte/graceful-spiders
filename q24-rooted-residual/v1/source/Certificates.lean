import Amalgamation
namespace GracefulBoundary

/-- All core sum permutations decode to the full upper difference band. -/
theorem decode_core_sums (p : Nat) (hp : 1 ≤ p) (sums : List Nat)
    (hs : sums.Perm (List.range (2*p-1))) :
    (sums.map (fun q => 4*p+6-q)).Perm (List.range' (2*p+8) (2*p-1)) := by
  have h := List.Perm.map (fun q => 4*p+6-q) hs
  have hr : (List.range' (2*p+8) (2*p-1)).reverse =
      (List.range (2*p-1)).map (fun q => 4*p+6-q) := by
    rw [List.reverse_range', show 2*p+8+(2*p-1)-1=4*p+6 by omega]
  rw [← hr] at h
  exact h.trans (List.reverse_perm _)

/-- Exact multiset composition for an arbitrary supplied core-sum partition.
    The identification with every edge of the raw shell path is still a separate
    structural proof obligation. -/
theorem shell_plus_core_differences (p : Nat) (hp : 1 ≤ p) (sums : List Nat)
    (hs : sums.Perm (List.range (2*p-1))) :
    (shellDiffs p ++ sums.map (fun q => 4*p+6-q)).Perm (List.range' 1 (4*p+6)) := by
  have h := (shell_differences_exact p).append (decode_core_sums p hp sums hs)
  have hr : List.range' 1 (2*p+7) ++ List.range' (2*p+8) (2*p-1) =
      List.range' 1 (4*p+6) := by
    rw [show 2*p+8=1+1*(2*p+7) by omega, List.range'_append]
    congr 1
    omega
  rw [hr] at h
  exact h

def coreLabels (M : Nat) (c : List Nat) : List Nat :=
  c.zipIdx.map (fun (x,i) => if i%2=0 then M-x else x)

def completePath (p : Nat) (c : List Nat) : List Nat :=
  (coreLabels (4*p+6) c ++ [3*p+3,p+1,3*p+4]).reverse ++ [2*p+2] ++
  (List.range p).flatMap (fun j => [2*p+3+j,2*p+1-j]) ++ [3*p+6,p,3*p+5]

def crosses (A : Nat) : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: xs => ((a ≤ A ∧ A < b) ∨ (b ≤ A ∧ A < a)) ∧ crosses A (b :: xs)

instance crossesDecidable (A : Nat) (c : List Nat) : Decidable (crosses A c) :=
  match c with
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | a :: b :: xs =>
    have : Decidable (crosses A (b :: xs)) := crossesDecidable A (b :: xs)
    inferInstanceAs (Decidable (((a ≤ A ∧ A < b) ∨ (b ≤ A ∧ A < a)) ∧ crosses A (b :: xs)))
def PathCertificate (s : Nat) (c : List Nat) : Prop :=
  c.length = 12*s+7 ∧ c.Perm (List.range (12*s+7)) ∧
  (edgeDiffs c).Perm (List.range' 1 (12*s+6)) ∧
  crosses (6*s+2) c ∧ c[6*s+3]? = some (6*s+2) ∧
  c[2*s+3]? = some 0 ∧ c[2*s+2]? = some (12*s+6)

instance (s : Nat) (c : List Nat) : Decidable (PathCertificate s c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem seed2_full_path : PathCertificate 2 (completePath 6 seed2) := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem seed3_full_path : PathCertificate 3 (completePath 9 seed3) := by decide

/-- Complementation preserves gracefulness for any indexed graph. -/
theorem graceful_complement {V E : Type} (G : IndexedGraph V E) (M : Nat)
    (f : V → Nat) (hf : Graceful G M f) : Graceful G M (fun v => M-f v) := by
  constructor
  · constructor
    · intro v; omega
    · intro v w he
      have hv := (hf.vertices.bounds v).2
      have hw := (hf.vertices.bounds w).2
      exact hf.vertices.injective v w (by omega)
    · intro x _ hx
      obtain ⟨v,hv⟩ := hf.vertices.onto (M-x) (by omega) (by omega)
      exact ⟨v, by simp [hv]; omega⟩
  · have he : weight G (fun v => M-f v) = weight G f := by
      funext e
      exact complement_difference M _ _ (hf.vertices.bounds _).2 (hf.vertices.bounds _).2
    rw [he]
    exact hf.edges

/-- The zero of an alpha input survives its identification with the residual
    graph, including the degenerate case where the zero is the shared vertex. -/
theorem graft_zero_anchor {V W : Type} (c : V) (d : W) (f : V → Nat) (g : W → Nat)
    (A Q : Nat) (hc : f c=A) (hd : g d=0) (v : V) (hv : f v=0) :
    graftLabel c f g A Q (graftEmbed c d v)=0 := by
  rw [graftLabel_embed c d f g A Q hc hd, hv]
  simp [alphaShift]

theorem graft_max_anchor {V W : Type} (c : V) (d : W) (f : V → Nat) (g : W → Nat)
    (A M Q : Nat) (hc : f c=A) (hd : g d=0) (hAM : A < M) (v : V) (hv : f v=M) :
    graftLabel c f g A Q (graftEmbed c d v)=M+Q := by
  rw [graftLabel_embed c d f g A Q hc hd, hv]
  simp [alphaShift, Nat.not_le.mpr hAM]

end GracefulBoundary

