import EvenAttachment

namespace GracefulBoundary.LabelOne

structure Twizzler (M : Nat) (c : List Nat) : Prop where
  length : c.length=M
  labels : c.Perm (List.range M)
  differences : (edgeDiffs c).Perm (List.range' 1 (M-1))
  first : c.head?=some (M-3)
  last : c.getLast?=some ((M-5)/2)

def T5 : List Nat := [2,3,1,4,0]
def T6 : List Nat := [3,2,4,1,5,0]
def T7 : List Nat := [4,2,3,6,0,5,1]
def T8 : List Nat := [5,2,4,3,7,0,6,1]
def T9 : List Nat := [6,0,8,1,4,5,3,7,2]
def T10 : List Nat := [7,0,9,1,5,4,6,3,8,2]
theorem T5_valid : Twizzler 5 T5 := by constructor <;> decide
theorem T6_valid : Twizzler 6 T6 := by constructor <;> decide
theorem T7_valid : Twizzler 7 T7 := by constructor <;> decide
theorem T8_valid : Twizzler 8 T8 := by constructor <;> decide
theorem T9_valid : Twizzler 9 T9 := by constructor <;> decide
theorem T10_valid : Twizzler 10 T10 := by constructor <;> decide

def twizzlerStep (M : Nat) (c : List Nat) : List Nat :=
  [M+3,2,M+4,1,M+5,0]++c.map (fun x => 3+x)

theorem translated_edges (s : Nat) (c : List Nat) : edgeDiffs (c.map (fun x => s+x))=edgeDiffs c := by
  induction c using edgeSums.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b c ih =>
    change distance (s+a) (s+b)::edgeDiffs ((b::c).map (fun x => s+x)) = _
    rw [ih,translate_difference]
    rfl

theorem twizzler_labels_step (M : Nat) :
    ([M+3,2,M+4,1,M+5,0]++List.range' 3 M).Perm (List.range (M+6)) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,count_band,Nat.beq_eq_true_eq]
  repeat (any_goals (first | omega | split))

theorem twizzler_edges_step (M : Nat) (hM : 5≤M) :
    ([M+1,M+2,M+3,M+4,M+5,M]++List.range' 1 (M-1)).Perm (List.range' 1 (M+5)) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_cons,List.count_nil,count_band,Nat.beq_eq_true_eq]
  repeat (any_goals (first | omega | split))

theorem twizzler_step_valid (M : Nat) (hM : 5≤M) (c : List Nat) (hc : Twizzler M c) :
    Twizzler (M+6) (twizzlerStep M c) := by
  have labels := (List.Perm.refl [M+3,2,M+4,1,M+5,0]).append (hc.labels.map (fun x => 3+x))
  rw [←List.range'_eq_map_range] at labels
  have edges : edgeDiffs (twizzlerStep M c)=[M+1,M+2,M+3,M+4,M+5,M]++edgeDiffs c := by
    obtain ⟨tail,he⟩ := List.head?_eq_some_iff.mp hc.first
    have first : 3+(M-3)=M := by omega
    dsimp only [twizzlerStep]
    rw [he,List.map_cons,first]
    simp only [List.cons_append,List.nil_append,edgeDiffs]
    have ht := translated_edges 3 ((M-3)::tail)
    rw [List.map_cons,first] at ht
    rw [←ht]
    have h1 : distance (M+3) 2=M+1 := by dsimp only [distance]; omega
    have h2 : distance 2 (M+4)=M+2 := by dsimp only [distance]; omega
    have h3 : distance (M+4) 1=M+3 := by dsimp only [distance]; omega
    have h4 : distance 1 (M+5)=M+4 := by dsimp only [distance]; omega
    have h5 : distance (M+5) 0=M+5 := by dsimp only [distance]; omega
    have h6 : distance 0 M=M := by dsimp only [distance]; omega
    simp only [h1,h2,h3,h4,h5,h6]
  refine ⟨by simp [twizzlerStep,hc.length],labels.trans (twizzler_labels_step M),?_,by simp [twizzlerStep],?_⟩
  · rw [edges]
    have perm := (List.Perm.refl [M+1,M+2,M+3,M+4,M+5,M]).append hc.differences
    have next := perm.trans (twizzler_edges_step M hM)
    simpa only [show M+6-1=M+5 by omega] using next
  · have endEq : 3+(M-5)/2=(M+6-5)/2 := by omega
    have mapped : (c.map (fun x => 3+x)).getLast?=some ((M+6-5)/2) := by
      rw [List.getLast?_map,hc.last]
      simp only [Option.map_some,endEq]
    dsimp only [twizzlerStep]
    rw [List.getLast?_append,mapped]
    rfl

theorem twizzlers : ∀ M,5≤M → ∃ c,Twizzler M c := by
  intro M
  induction M using Nat.strongRecOn with
  | ind M ih =>
    intro hM
    by_cases small : M≤10
    · have cases : M=5 ∨ M=6 ∨ M=7 ∨ M=8 ∨ M=9 ∨ M=10 := by omega
      rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨T5,T5_valid⟩
      · exact ⟨T6,T6_valid⟩
      · exact ⟨T7,T7_valid⟩
      · exact ⟨T8,T8_valid⟩
      · exact ⟨T9,T9_valid⟩
      · exact ⟨T10,T10_valid⟩
    · obtain ⟨c,hc⟩ := ih (M-6) (by omega) (by omega)
      have next := twizzler_step_valid (M-6) (by omega) c hc
      rw [show M-6+6=M by omega] at next
      exact ⟨twizzlerStep (M-6) c,next⟩

theorem anchored_permutations (M : Nat) (hM : 5≤M) :
    ∃ c,c.length=M ∧ c.Perm (List.range M) ∧
      (edgeDiffs c).Perm (List.range' 1 (M-1)) ∧ c.head?=some ((M-5)/2) := by
  obtain ⟨c,hc⟩ := twizzlers M hM
  refine ⟨c.reverse,by simp [hc.length],(List.reverse_perm _).trans hc.labels,?_,?_⟩
  · rw [edgeDiffs_reverse]
    exact (List.reverse_perm _).trans hc.differences
  · simpa only [List.head?_reverse] using hc.last

end GracefulBoundary.LabelOne
