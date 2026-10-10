import Std

/-! Private formal bridge. No uniform raw-sequence recurrence theorem is assumed.
All finite examples below use kernel `decide`, not native evaluation. -/
namespace GracefulBoundary

def distance (a b : Nat) : Nat := a - b + (b - a)

def edgeSums : List Nat → List Nat
  | [] => []
  | [_] => []
  | a :: b :: xs => (a + b) :: edgeSums (b :: xs)

def edgeDiffs : List Nat → List Nat
  | [] => []
  | [_] => []
  | a :: b :: xs => distance a b :: edgeDiffs (b :: xs)

def highs : List Nat → List Nat
  | [] => []
  | [a] => [a]
  | a :: _ :: xs => a :: highs xs

def lows : List Nat → List Nat
  | [] => []
  | [_] => []
  | _ :: b :: xs => b :: lows xs

def CoreInvariant (s : Nat) (c : List Nat) : Prop :=
  2 ≤ s ∧ c.length = 6*s ∧
  (highs c).Perm (List.range (3*s)) ∧
  (lows c).Perm (List.range (3*s)) ∧
  (edgeSums c).Perm (List.range (6*s-1)) ∧
  c[0]? = some 3 ∧ c[6*s-1]? = some (3*s-4) ∧
  c[4*s-2]? = some 4 ∧ c[4*s-1]? = some 0 ∧
  c[4*s]? = some 0 ∧ c[4*s+1]? = some 1

instance (s : Nat) (c : List Nat) : Decidable (CoreInvariant s c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def seed2 : List Nat := [3,3,2,5,5,4,4,0,0,1,1,2]
def seed3 : List Nat := [3,6,6,7,7,8,8,3,2,4,4,0,0,1,1,2,5,5]

theorem seed2_valid : CoreInvariant 2 seed2 := by decide
theorem seed3_valid : CoreInvariant 3 seed3 := by decide

def bump (x : Nat) := if x = 0 then 0 else x+6

def extend (s : Nat) (c : List Nat) : List Nat :=
  [3,5,6,3,2,4] ++ (c.take (4*s-1)).map bump ++ [6,4,0,0,1,1,2,5] ++
  (c.drop (4*s+1)).map bump

theorem first_even_step_valid : CoreInvariant 4 (extend 2 seed2) := by decide
theorem first_odd_step_valid : CoreInvariant 5 (extend 3 seed3) := by decide

/-- Each positive old vertex moves into the complementary high band. -/
theorem bump_positive (x : Nat) (hx : 0 < x) : bump x = x+6 := by
  simp [bump, Nat.ne_of_gt hx]

theorem old_positive_band (p x : Nat) :
    (∃ y, 1 ≤ y ∧ y < p ∧ x = y+6) ↔ 7 ≤ x ∧ x < p+6 := by
  constructor
  · rintro ⟨y, hy, hp, rfl⟩; omega
  · intro h; exact ⟨x-6, by omega, by omega, by omega⟩

/-- Exact finite inserted-side multisets. -/
theorem high_gadget : ([3,6,2,4,1,5] : List Nat).Perm (List.range' 1 6) := by decide
theorem low_gadget : ([5,3,4,6,1,2] : List Nat).Perm (List.range' 1 6) := by decide

def insertedSums : List Nat := [8,11,9,5,6,13,16,10,4,1,2,3,7,12]
theorem inserted_sums_exact : insertedSums.Perm (List.range' 1 13 ++ [16]) := by decide

/-- The fourteen new edge sums, with all three bridges, computed from
    the actual P/B/D numeric vertices and shifted old neighbours. -/
theorem gadget_edges :
    edgeSums [3,5,6,3,2,4,9] ++ edgeSums [10,6,4,0] ++
      edgeSums [0,1,1,2,5,7] = insertedSums := by decide

/-- The shift maps each retained old sum to precisely the required band. -/
theorem retained_sum_range (p x : Nat) (hp : 3 ≤ p) :
    (∃ q, q ≤ 2*p-2 ∧ q ≠ 0 ∧ q ≠ 1 ∧ q ≠ 4 ∧ x = q+12) ↔
      x = 14 ∨ x = 15 ∨ (17 ≤ x ∧ x ≤ 2*p+10) := by
  constructor
  · rintro ⟨q, hq, h0, h1, h4, rfl⟩; omega
  · intro hx; exact ⟨x-12, by omega, by omega, by omega, by omega, by omega⟩

/-- Exact all-parameter coverage, including disjointness, of the
    retained zero, inserted sums, and shifted retained positive sums. -/
theorem recurrence_sum_partition (p x : Nat) (hp : 3 ≤ p) :
    ((x = 0 ∨ (1 ≤ x ∧ x ≤ 13) ∨ x = 16) ∨
      (x = 14 ∨ x = 15 ∨ (17 ≤ x ∧ x ≤ 2*p+10))) ↔ x ≤ 2*p+10 := by omega

theorem recurrence_sum_disjoint (p x : Nat) :
    ¬ ((x = 0 ∨ (1 ≤ x ∧ x ≤ 13) ∨ x = 16) ∧
      (x = 14 ∨ x = 15 ∨ (17 ≤ x ∧ x ≤ 2*p+10))) := by omega

theorem shifted_sum_injective (a b : Nat) (h : a+12 = b+12) : a = b := by omega

theorem shifted_edge_sum (a b : Nat) : (a+6)+(b+6) = (a+b)+12 := by omega

theorem next_anchor_index (s : Nat) (hs : 2 ≤ s) :
    (4*s-1)+8 = 4*(s+2)-1 ∧ (4*s)+8 = 4*(s+2) := by omega

theorem next_last_value (s : Nat) (hs : 2 ≤ s) :
    bump (3*s-4) = 3*(s+2)-4 := by
  rw [bump_positive _ (by omega)]; omega

/-- Two seeds and a genuinely proved +2 step suffice for all s>=2.
    This theorem is conditional; it does not supply the step. -/
theorem induction_from_two_seeds (P : Nat → Prop)
    (h2 : P 2) (h3 : P 3) (step : ∀ s, 2 ≤ s → P s → P (s+2)) :
    ∀ s, 2 ≤ s → P s := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro hs
    by_cases htwo : s=2
    · simpa [htwo] using h2
    by_cases hthree : s=3
    · simpa [hthree] using h3
    have hsmall : s-2 < s := by omega
    have hbase : 2 ≤ s-2 := by omega
    have hprev := ih (s-2) hsmall hbase
    have hnext := step (s-2) hbase hprev
    simpa [show s-2+2=s by omega] using hnext

/-- Difference arithmetic for every core edge after high-offset decoding. -/
theorem core_difference (p h l : Nat) (hh : h < p) (hl : l < p) :
    distance (4*p+6-h) l = 4*p+6-(h+l) := by unfold distance; omega

theorem core_difference_band (p q : Nat) (hp : 1 ≤ p) (hq : q ≤ 2*p-2) :
    2*p+8 ≤ 4*p+6-q ∧ 4*p+6-q ≤ 4*p+6 := by omega

/-- Numeric partition of the non-core shell edge differences. -/
def shellDiffs (p : Nat) : List Nat := List.range' 1 (2*p) ++
  [2*p+1,2*p+7,2*p+2,2*p+3,2*p+4,2*p+6,2*p+5]

theorem count_band (x start size : Nat) :
    (List.range' start size).count x = if start ≤ x ∧ x < start+size then 1 else 0 := by
  rw [List.count_range']
  congr 1
  apply propext
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨x-start, by omega, by omega⟩

theorem shell_differences_exact (p : Nat) :
    (shellDiffs p).Perm (List.range' 1 (2*p+7)) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [shellDiffs, List.count_append, List.count_cons, List.count_nil, count_band, Nat.beq_eq_true_eq]
  repeat (any_goals split)
  all_goals omega

/-- The piecewise alpha shift used in amalgamation. -/
def alphaShift (A Q x : Nat) : Nat := if x ≤ A then x else x+Q

theorem alphaShift_injective (A Q x y : Nat)
    (h : alphaShift A Q x = alphaShift A Q y) : x=y := by
  unfold alphaShift at h; split at h <;> split at h <;> omega

theorem alphaShift_crossing (A Q low high : Nat)
    (hl : low ≤ A) (hh : A < high) :
    distance (alphaShift A Q high) (alphaShift A Q low) =
      distance high low + Q := by simp [alphaShift, hl, Nat.not_le.mpr hh, distance]; omega

theorem translate_difference (A x y : Nat) :
    distance (A+x) (A+y) = distance x y := by unfold distance; omega

theorem mixed_label_collision (A Q x b : Nat) (hb : b ≤ Q) :
    alphaShift A Q x = A+b ↔ x=A ∧ b=0 := by
  unfold alphaShift; split <;> omega

theorem amalgam_label_coverage (A M Q x : Nat) (hAM : A ≤ M) (hx : x ≤ M+Q) :
    (∃ b, b ≤ Q ∧ x=A+b) ∨ (∃ y, y ≤ M ∧ y ≠ A ∧ x=alphaShift A Q y) := by
  by_cases hlo : x < A
  · right; refine ⟨x, by omega, by omega, ?_⟩; simp [alphaShift, show x ≤ A by omega]
  by_cases hmid : x ≤ A+Q
  · left; exact ⟨x-A, by omega, by omega⟩
  · right; refine ⟨x-Q, by omega, by omega, ?_⟩
    simp [alphaShift, show ¬ x-Q ≤ A by omega]; omega

theorem complement_difference (M x y : Nat) (hx : x ≤ M) (hy : y ≤ M) :
    distance (M-x) (M-y) = distance x y := by unfold distance; omega

theorem complement_max_zero (M : Nat) : M-M=0 := by omega

end GracefulBoundary



