import SignedCap

/-! Proposed companion valley; the unbounded inventory theorem remains a separate gate. -/
namespace GracefulSignedCap

def L : Nat → List Nat
  | 0 => [1,0]
  | t+1 => [3*(t+1)+1,3*(t+1)] ++ L t

def A : Nat → List Nat
  | 0 => []
  | t+1 => A t ++ [3*t+2,3*t+3]

def D : Nat → List Nat
  | 0 => [1]
  | t+1 => [3*t+4,3*t+2] ++ D t

def valley (t : Nat) : List Int :=
  ((L t) ++ [0] ++ (A t) ++ [3*t+2,3*t+3,3*t+4,3*t+2] ++ (D t)).map Int.ofNat

structure ValleyContract (t : Nat) : Prop where
  length : (valley t).length=6*t+8
  first : (valley t).head?=some (Int.ofNat (3*t+1))
  terminal : (valley t)[6*t+7]?=some 1
  lowSide : (highs (valley t)).Perm (band (3*t+4))
  highSide : (lows (valley t)).Perm (band (3*t+3) ++ [Int.ofNat (3*t+4)])
  sums : (edgeSums (valley t)).Perm
    (band (6*t+4) ++ [Int.ofNat (6*t+5),Int.ofNat (6*t+6),Int.ofNat (6*t+7)])
  zeros : (valley t)[2*t+1]?=some 0 ∧ (valley t)[2*t+2]?=some 0

theorem L_length (t : Nat) : (L t).length=2*(t+1) := by
  induction t with
  | zero => decide
  | succ t ih => simp [L, ih]; omega

theorem A_length (t : Nat) : (A t).length=2*t := by
  induction t with
  | zero => decide
  | succ t ih => simp [A, ih]; omega

theorem D_length (t : Nat) : (D t).length=2*t+1 := by
  induction t with
  | zero => decide
  | succ t ih => simp [D, ih]; omega

theorem valley_length (t : Nat) : (valley t).length=6*t+8 := by
  simp [valley, L_length, A_length, D_length]
  omega

theorem L_last_zero (t : Nat) : (L t)[2*t+1]?=some 0 := by
  induction t with
  | zero => decide
  | succ t ih =>
    simpa [L, show 2*(t+1)+1=(2*t+1)+2 by omega] using ih

theorem valley_zeros (t : Nat) :
    (valley t)[2*t+1]?=some 0 ∧ (valley t)[2*t+2]?=some 0 := by
  let tail : List Nat := [0] ++ A t ++ [3*t+2,3*t+3,3*t+4,3*t+2] ++ D t
  have eqv : valley t = (L t ++ tail).map Int.ofNat := by
    simp [valley,tail,List.append_assoc]
  rw [eqv]
  constructor
  · simp only [List.getElem?_map]
    rw [List.getElem?_append_left (by rw [L_length]; omega), L_last_zero]
    rfl
  · simp only [List.getElem?_map]
    rw [List.getElem?_append_right (by rw [L_length]; omega)]
    have index : 2*t+2-(L t).length=0 := by rw [L_length]; omega
    rw [index]
    simp [tail]

theorem valley5_valid : ValleyContract 5 := by constructor <;> decide

end GracefulSignedCap
