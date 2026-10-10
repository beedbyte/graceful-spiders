import H1Concrete
namespace GracefulBoundary.H1Concrete

theorem lengths (s : Nat) : (A s).length=2*s ∧ (B s).length=2*s ∧ (D s).length=2*s := by
  induction s with
  | zero => decide
  | succ s ih => simp only [A,B,D,List.length_append,List.length_cons,List.length_nil,ih.1,ih.2.1,ih.2.2]; omega

theorem A_lookup (s i : Nat) (hi : i<2*s) :
    (A s)[i]?=some (3*(i/2)+1+i%2) := by
  induction s with
  | zero => omega
  | succ s ih =>
    rw [A]
    by_cases old : i<2*s
    · rw [List.getElem?_append_left (by rw [(lengths s).1]; exact old)]
      exact ih old
    · rw [List.getElem?_append_right (by rw [(lengths s).1]; omega),(lengths s).1]
      have cases : i=2*s ∨ i=2*s+1 := by omega
      rcases cases with rfl|rfl <;> simp only [show 2*s-2*s=0 by omega,
        show 2*s+1-2*s=1 by omega,List.getElem?_cons_zero,List.getElem?_cons_succ]
      all_goals congr 1 <;> omega

theorem D_lookup (s i : Nat) (hi : i<2*s) :
    (D s)[i]?=some (3*(i/2)+i%2) := by
  induction s with
  | zero => omega
  | succ s ih =>
    rw [D]
    by_cases old : i<2*s
    · rw [List.getElem?_append_left (by rw [(lengths s).2.2]; exact old)]
      exact ih old
    · rw [List.getElem?_append_right (by rw [(lengths s).2.2]; omega),(lengths s).2.2]
      have cases : i=2*s ∨ i=2*s+1 := by omega
      rcases cases with rfl|rfl <;> simp only [show 2*s-2*s=0 by omega,
        show 2*s+1-2*s=1 by omega,List.getElem?_cons_zero,List.getElem?_cons_succ]
      all_goals congr 1 <;> omega

theorem B_lookup (s i : Nat) (hi : i<2*s) :
    (B s)[i]?=some (3*s-1-3*(i/2)-2*(i%2)) := by
  induction s generalizing i with
  | zero => omega
  | succ s ih =>
    by_cases hz : i=0
    · subst i; simp only [B,List.cons_append,List.getElem?_cons_zero]; congr 1 <;> omega
    by_cases ho : i=1
    · subst i; simp only [B,List.cons_append,List.getElem?_cons_succ,List.getElem?_cons_zero]; congr 1 <;> omega
    have hj : i-2<2*s := by omega
    rw [B,List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega)]
    simp only [List.length_cons,List.length_nil]
    rw [ih (i-2) hj]
    congr 1
    omega

def coreValue (s i : Nat) : Nat :=
  if i<2*s then 3*(i/2)+1+i%2
  else if i<4*s then 3*s-1-3*((i-2*s)/2)-2*((i-2*s)%2)
  else 3*((i-4*s)/2)+(i-4*s)%2

theorem chunks_lookup (s i : Nat) (hi : i<6*s) :
    (chunks s)[i]?=some (coreValue s i) := by
  have lab : (A s++B s).length=4*s := by simp only [List.length_append,(lengths s).1,(lengths s).2.1]; omega
  unfold chunks coreValue
  by_cases ha : i<2*s
  · rw [List.getElem?_append_left (by rw [lab]; omega),
      List.getElem?_append_left (by rw [(lengths s).1]; omega),A_lookup s i ha]
    simp only [ha,ite_true]
  · by_cases hb : i<4*s
    · rw [List.getElem?_append_left (by rw [lab]; omega),
        List.getElem?_append_right (by rw [(lengths s).1]; omega),(lengths s).1,
        B_lookup s (i-2*s) (by omega)]
      simp only [ha,hb,ite_false,ite_true]
    · rw [List.getElem?_append_right (by rw [lab]; omega),lab,D_lookup s (i-4*s) (by omega)]
      simp only [ha,hb,ite_false]

theorem half_length (s : Nat) : (H1Append.halfCore s).length=3*s := by
  simp [H1Append.halfCore]

theorem concrete_length (s : Nat) : (H1Append.concreteCore s).length=6*s := by
  simp only [H1Append.concreteCore,List.length_append,List.length_map,List.length_reverse,half_length]
  omega

theorem half_lookup (s i : Nat) (hi : i<3*s) :
    (H1Append.halfCore s)[i]?=some (if i%2=0 then H1Append.permutationValue s i else 3*s-1-H1Append.permutationValue s i) := by
  simp [H1Append.halfCore,hi]

theorem concrete_lookup (s i : Nat) (hi : i<6*s) :
    (H1Append.concreteCore s)[i]?=some (coreValue s i) := by
  unfold H1Append.concreteCore
  by_cases first : i<3*s
  · rw [List.getElem?_append_left (by rw [half_length]; exact first),half_lookup s i first]
    unfold H1Append.permutationValue coreValue
    repeat (any_goals split)
    all_goals congr 1 <;> omega
  · rw [List.getElem?_append_right (by rw [half_length]; omega),half_length,List.getElem?_map]
    have hj : 6*s-1-i<3*s := by omega
    have hr : ((H1Append.halfCore s).reverse)[i-3*s]?=(H1Append.halfCore s)[6*s-1-i]? := by
      exact List.getElem?_reverse' (by rw [half_length]; omega)
    rw [hr,half_lookup s (6*s-1-i) hj]
    simp only [Option.map_some]
    unfold H1Append.permutationValue coreValue
    repeat (any_goals split)
    all_goals congr 1 <;> omega

theorem concrete_eq_chunks (s : Nat) : H1Append.concreteCore s=chunks s := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<6*s
  · rw [concrete_lookup s i hi,chunks_lookup s i hi]
  · have len : (chunks s).length=6*s := by
      simp only [chunks,List.length_append,(lengths s).1,(lengths s).2.1,(lengths s).2.2]; omega
    rw [List.getElem?_eq_none (by rw [concrete_length]; omega),List.getElem?_eq_none (by rw [len]; omega)]

end GracefulBoundary.H1Concrete
