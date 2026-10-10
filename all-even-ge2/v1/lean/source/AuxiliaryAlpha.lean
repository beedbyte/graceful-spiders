import AllArmsEight
namespace GracefulBoundary.EvenUniform

structure Auxiliary (r : Nat) (c : List Nat) : Prop where
  lower : 3≤r
  length : c.length=2*r-1
  low : (highs c).Perm (0::List.range' 2 (r-1))
  high : (lows c).Perm (List.range (r-1))
  sums : (edgeSums c).Perm (List.range' 1 (2*r-2))
  first : c.head?=some 0
  last : c.getLast?=some (r-1)

def Terminal (r : Nat) (c : List Nat) : Prop := ∃u,u.length=2*r-5 ∧ c=u++[r-2,r,r-3,r-1]
def StrongAuxiliary (r : Nat) (c : List Nat) := Auxiliary r c ∧ Terminal r c
def A3 : List Nat := [0,1,3,0,2]
def A4 : List Nat := [0,1,2,0,4,2,3]
def A5 : List Nat := [0,1,3,0,2,3,5,2,4]
def A7 : List Nat := [0,1,3,0,2,3,5,2,4,5,7,4,6]

theorem A3_valid : StrongAuxiliary 3 A3 := by
  constructor
  · constructor <;> decide
  · exact ⟨[0],by decide,by decide⟩
theorem A4_valid : Auxiliary 4 A4 := by constructor <;> decide
theorem A5_valid : StrongAuxiliary 5 A5 := by
  constructor
  · constructor <;> decide
  · exact ⟨[0,1,3,0,2],by decide,by decide⟩
theorem A7_valid : StrongAuxiliary 7 A7 := by
  constructor
  · constructor <;> decide
  · exact ⟨[0,1,3,0,2,3,5,2,4],by decide,by decide⟩

def replacement (r : Nat) : List Nat := [r-2,r-1,r-3,r+1,r-1,r,r+1,r+3,r,r+2]
def nextAuxiliary (r : Nat) (u : List Nat) := u++replacement r

theorem r3_retained_join : edgeSums ([0]++[3-2])=[1] := rfl
theorem r3_replacement_interval : (edgeSums (replacement 3)).Perm (List.range' 2 9) := by decide

theorem terminal_replacement_sums (r : Nat) (hr : 3≤r) :
    edgeSums [r-2,r,r-3,r-1]=[2*r-2,2*r-3,2*r-4] ∧
    edgeSums (replacement r)=[2*r-3,2*r-4,2*r-2,2*r,2*r-1,2*r+1,2*r+4,2*r+3,2*r+2] := by
  dsimp only [replacement,edgeSums]
  constructor <;> simp only [List.cons.injEq] <;> repeat (any_goals (first | omega | constructor))

theorem auxiliary_step (r : Nat) (c : List Nat) (hc : StrongAuxiliary r c) :
    ∃d,StrongAuxiliary (r+3) d := by
  obtain ⟨u,lu,shape⟩ := hc.2
  have hr := hc.1.lower
  have odd : u.length%2≠0 := by omega
  have hlo := hc.1.low.count_eq
  have hhi := hc.1.high.count_eq
  have hs := hc.1.sums.count_eq
  refine ⟨nextAuxiliary r u,?_,?_⟩
  · constructor
    · omega
    · simp only [nextAuxiliary,List.length_append,replacement,List.length_cons,List.length_nil,lu]; omega
    · apply List.perm_iff_count.mpr
      intro x
      have old := hlo x
      rw [shape,highs_append,ite_eq_right odd] at old
      simp only [lows,List.count_append,List.count_cons,List.count_nil,count_band,Nat.beq_eq_true_eq] at old
      dsimp only [nextAuxiliary]
      rw [highs_append,ite_eq_right odd]
      simp only [replacement,lows,List.count_append,List.count_cons,List.count_nil,count_band,Nat.beq_eq_true_eq]
      repeat (any_goals (first | omega | split at *))
    · apply List.perm_iff_count.mpr
      intro x
      have old := hhi x
      rw [shape,lows_append,ite_eq_right odd] at old
      simp only [highs,List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq] at old
      dsimp only [nextAuxiliary]
      rw [lows_append,ite_eq_right odd]
      simp only [replacement,highs,List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq]
      repeat (any_goals (first | omega | split at *))
    · apply List.perm_iff_count.mpr
      intro x
      have old := hs x
      rw [shape,edgeSums_overlap,(terminal_replacement_sums r hr).1] at old
      simp only [List.count_append,List.count_cons,List.count_nil,count_band,Nat.beq_eq_true_eq] at old
      dsimp only [nextAuxiliary,replacement]
      rw [edgeSums_overlap]
      change (edgeSums (u++[r-2])++edgeSums (replacement r)).count x=_
      rw [(terminal_replacement_sums r hr).2]
      simp only [List.count_append,List.count_cons,List.count_nil,count_band,Nat.beq_eq_true_eq]
      repeat (any_goals (first | omega | split at *))
    · have old := hc.1.first
      rw [shape] at old
      cases u with
      | nil => simp at lu; omega
      | cons a u =>
        simp only [List.cons_append,List.head?_cons,Option.some.injEq] at old
        simp only [nextAuxiliary,List.cons_append,List.head?_cons,old]
    · simp only [nextAuxiliary,replacement,List.getLast?_append,List.getLast?_cons]
      congr 1
  · refine ⟨u++[r-2,r-1,r-3,r+1,r-1,r],?_,?_⟩
    · simp only [List.length_append,List.length_cons,List.length_nil,lu]; omega
    · dsimp only [nextAuxiliary,replacement]
      have h0 : r+3-2=r+1 := by omega
      have h1 : r+3-3=r := by omega
      have h2 : r+3-1=r+2 := by omega
      simp only [h0,h1,h2,List.append_assoc,List.cons_append,List.nil_append]

theorem strong_auxiliaries : ∀r,3≤r → r≠4 → ∃c,StrongAuxiliary r c := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro hr h4
    by_cases small : r≤7
    · have cases : r=3 ∨ r=5 ∨ r=6 ∨ r=7 := by omega
      rcases cases with rfl|rfl|rfl|rfl
      · exact ⟨A3,A3_valid⟩
      · exact ⟨A5,A5_valid⟩
      · exact auxiliary_step 3 A3 A3_valid
      · exact ⟨A7,A7_valid⟩
    · obtain ⟨c,hc⟩ := ih (r-3) (by omega) (by omega) (by omega)
      obtain ⟨d,hd⟩ := auxiliary_step (r-3) c hc
      have eq : r-3+3=r := by omega
      simpa only [eq] using (show ∃d,StrongAuxiliary (r-3+3) d from ⟨d,hd⟩)

theorem auxiliaries (r : Nat) (hr : 3≤r) : ∃c,Auxiliary r c := by
  by_cases four : r=4
  · subst r; exact ⟨A4,A4_valid⟩
  · obtain ⟨c,hc⟩ := strong_auxiliaries r hr four; exact ⟨c,hc.1⟩

end GracefulBoundary.EvenUniform
