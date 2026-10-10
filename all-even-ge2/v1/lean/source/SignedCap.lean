import Std

/-! Private additive formalization of the proposed signed cap recurrence. -/
namespace GracefulSignedCap

def highs : List Int → List Int
  | [] => []
  | [a] => [a]
  | a :: _ :: xs => a :: highs xs

def lows : List Int → List Int
  | [] => []
  | [_] => []
  | _ :: b :: xs => b :: lows xs

def edgeSums : List Int → List Int
  | [] => []
  | [_] => []
  | a :: b :: xs => (a+b) :: edgeSums (b::xs)

def band (n : Nat) : List Int := (List.range n).map Int.ofNat

structure Cap (h : Nat) (c : List Int) : Prop where
  length : c.length=2*h+3
  root : c.head?=some (Int.ofNat (h+1))
  firstHigh : c[1]?=some (Int.ofNat (h-2))
  terminal : c[2*h+2]?=some (-2)
  lowSide : (lows c).Perm ((-1)::band h)
  highSide : (highs c).Perm (Int.ofNat (h+1)::(-2)::band h)
  sums : (edgeSums c).Perm ((-2)::(-1)::band (2*h))

def E3 : List Int := [4,1,1,2,2,-1,0,0,-2]
def E4 : List Int := [5,2,3,3,1,-1,0,1,2,0,-2]

theorem E3_valid : Cap 3 E3 := by constructor <;> decide
theorem E4_valid : Cap 4 E4 := by constructor <;> decide

def step (h : Nat) (c : List Int) : List Int :=
  [Int.ofNat (h+3),Int.ofNat h,Int.ofNat h,Int.ofNat (h+1),Int.ofNat (h+1)] ++ c.drop 1

theorem band_succ2 (n : Nat) : band (n+2)=band n ++ [Int.ofNat n,Int.ofNat (n+1)] := by
  simp [band, List.range_succ]

theorem step_length (h : Nat) (c : List Int) (hc : Cap h c) :
    (step h c).length=2*(h+2)+3 := by
  simp [step, hc.length]
  omega

theorem step_lows (h : Nat) (a b : Int) (xs : List Int) :
    lows (step h (a::b::xs)) = [Int.ofNat h,Int.ofNat (h+1)] ++ lows (a::b::xs) := by
  rfl

theorem step_highs (h : Nat) (a b : Int) (xs : List Int) :
    highs (step h (a::b::xs)) = [Int.ofNat (h+3),Int.ofNat h,Int.ofNat (h+1)] ++ (highs (a::b::xs)).drop 1 := by
  rfl

theorem band_succ4 (n : Nat) :
    band (n+4)=band n ++ [Int.ofNat n,Int.ofNat (n+1),Int.ofNat (n+2),Int.ofNat (n+3)] := by
  simp [show n+4=(n+2)+2 by omega, band_succ2, List.append_assoc]
  omega

theorem step_sums (h : Nat) (b : Int) (xs : List Int) :
    edgeSums (step h (Int.ofNat (h+1)::b::xs)) =
      [Int.ofNat (2*h+3),Int.ofNat (2*h),Int.ofNat (2*h+1),Int.ofNat (2*h+2)] ++
      edgeSums (Int.ofNat (h+1)::b::xs) := by
  simp [step, edgeSums]
  congr 1 <;> omega

theorem cap_prefix (h : Nat) (c : List Int) (hc : Cap h c) :
    ∃xs,c=Int.ofNat (h+1)::Int.ofNat (h-2)::xs := by
  cases c with
  | nil => have impossible := hc.root; simp at impossible
  | cons a rest =>
    cases rest with
    | nil => have impossible := hc.firstHigh; simp at impossible
    | cons b xs =>
      have ha : a=Int.ofNat (h+1) := by simpa using hc.root
      have hb : b=Int.ofNat (h-2) := by simpa using hc.firstHigh
      exact ⟨xs,by simp [ha,hb]⟩

theorem step_lowSide (h : Nat) (c : List Int) (hc : Cap h c) :
    (lows (step h c)).Perm ((-1)::band (h+2)) := by
  obtain ⟨xs,rfl⟩ := cap_prefix h c hc
  apply List.perm_iff_count.mpr
  intro x
  have old := hc.lowSide.count_eq x
  simp only [step_lows, band_succ2, List.count_append, List.count_cons] at old ⊢
  omega

theorem step_highSide (h : Nat) (c : List Int) (hc : Cap h c) :
    (highs (step h c)).Perm (Int.ofNat (h+3)::(-2)::band (h+2)) := by
  obtain ⟨xs,rfl⟩ := cap_prefix h c hc
  apply List.perm_iff_count.mpr
  intro x
  have old := hc.highSide.count_eq x
  simp [step_highs, highs, band_succ2, List.count_append, List.count_cons] at old ⊢
  omega

theorem step_sumSide (h : Nat) (c : List Int) (hc : Cap h c) :
    (edgeSums (step h c)).Perm ((-2)::(-1)::band (2*(h+2))) := by
  obtain ⟨xs,rfl⟩ := cap_prefix h c hc
  rw [step_sums]
  apply List.perm_iff_count.mpr
  intro x
  have old := hc.sums.count_eq x
  have sizes : 2*(h+2)=2*h+4 := by omega
  simp [sizes, band_succ4, List.count_append, List.count_cons] at old ⊢
  omega

theorem step_terminal (h : Nat) (c : List Int) (hc : Cap h c) :
    (step h c)[2*(h+2)+2]?=some (-2) := by
  obtain ⟨xs,rfl⟩ := cap_prefix h c hc
  have old := hc.terminal
  simp [step] at old ⊢
  exact old

theorem step_valid (h : Nat) (_hh : 3≤h) (c : List Int) (hc : Cap h c) :
    Cap (h+2) (step h c) := by
  refine ⟨step_length h c hc, ?_, ?_, step_terminal h c hc,
    step_lowSide h c hc, step_highSide h c hc, step_sumSide h c hc⟩
  · simp [step]
    omega
  · simp [step]

theorem exists_cap (h : Nat) (hh : 3≤h) : ∃c,Cap h c := by
  have both : ∀t : Nat, (∃c,Cap (t+3) c) ∧ (∃c,Cap (t+4) c) := by
    intro t
    induction t with
    | zero => exact ⟨⟨E3,E3_valid⟩,⟨E4,E4_valid⟩⟩
    | succ t ih =>
      rcases ih with ⟨⟨c3,h3⟩,⟨c4,h4⟩⟩
      constructor
      · exact ⟨c4,by simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h4⟩
      · exact ⟨step (t+3) c3,by simpa [Nat.succ_eq_add_one, Nat.add_assoc] using step_valid (t+3) (by omega) c3 h3⟩
  have eq : h-3+3=h := by omega
  simpa [eq] using (both (h-3)).1

end GracefulSignedCap
