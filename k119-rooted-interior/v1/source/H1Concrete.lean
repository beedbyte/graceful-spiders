import H1Append
namespace GracefulBoundary.H1Concrete

def A : Nat → List Nat
  | 0 => []
  | s+1 => A s ++ [3*s+1,3*s+2]
def B : Nat → List Nat
  | 0 => []
  | s+1 => [3*s+2,3*s] ++ B s
def D : Nat → List Nat
  | 0 => []
  | s+1 => D s ++ [3*s,3*s+1]
def chunks (s : Nat) := A s ++ B s ++ D s

structure Triple (s : Nat) (a b d : List Nat) : Prop where
  positive : 1≤s
  la : a.length=2*s
  lb : b.length=2*s
  ld : d.length=2*s
  ah : a.head?=some 1
  lastA : a.getLast?=some (3*s-1)
  bh : b.head?=some (3*s-1)
  bt : b.getLast?=some 0
  dh : d.head?=some 0
  dt : d.getLast?=some (3*s-2)
  high : (highs (a++b++d)).Perm (List.range (3*s))
  low : (lows (a++b++d)).Perm (List.range (3*s))
  sums : (edgeSums (a++b++d)).Perm (List.range (6*s-1))

theorem head_append (a b : List Nat) (x : Nat) (h : a.head?=some x) :
    (a++b).head?=some x := by
  obtain ⟨as,ha⟩ := List.head?_eq_some_iff.mp h
  simp [ha]

theorem last_append (a b : List Nat) (x : Nat) (h : b.getLast?=some x) :
    (a++b).getLast?=some x := by
  rw [List.getLast?_append,h]
  rfl

theorem join (a b : List Nat) (x y : Nat) (ha : a.getLast?=some x) (hb : b.head?=some y) :
    edgeSums (a++b)=edgeSums a ++ (x+y)::edgeSums b := by
  obtain ⟨bs,hb⟩ := List.head?_eq_some_iff.mp hb
  rw [hb,edgeSums_join a x y bs ha]

set_option maxHeartbeats 2000000 in
theorem triple_step (s : Nat) (a b d : List Nat) (h : Triple s a b d) :
    Triple (s+1) (a++[3*s+1,3*s+2]) ([3*s+2,3*s]++b) (d++[3*s,3*s+1]) := by
  have hs := h.positive
  have ae : a.length%2=0 := by rw [h.la]; omega
  have de : d.length%2=0 := by rw [h.ld]; omega
  have nae : (a++[3*s+1,3*s+2]).length%2=0 := by simp only [List.length_append,h.la,List.length_cons,List.length_nil]; omega
  have ab : (a++b).length%2=0 := by simp only [List.length_append,h.la,h.lb]; omega
  have nab : (a++[3*s+1,3*s+2]++([3*s+2,3*s]++b)).length%2=0 := by
    simp only [List.length_append,h.la,h.lb,List.length_cons,List.length_nil]; omega
  have nablast : (a++[3*s+1,3*s+2]++([3*s+2,3*s]++b)).getLast?=some 0 :=
    last_append _ _ _ (last_append _ _ _ h.bt)
  have oldedges : edgeSums (a++b++d)=edgeSums a ++ (6*s-2)::edgeSums b ++ 0::edgeSums d := by
    rw [join (a++b) d 0 0 (last_append a b 0 h.bt) h.dh,
      join a b (3*s-1) (3*s-1) h.lastA h.bh]
    simp only [show 3*s-1+(3*s-1)=6*s-2 by omega,List.append_assoc,Nat.zero_add]
  have newedges : edgeSums (a++[3*s+1,3*s+2]++([3*s+2,3*s]++b)++(d++[3*s,3*s+1])) =
      edgeSums a ++ [6*s,6*s+3,6*s+4,6*s+2,6*s-1] ++ edgeSums b ++ [0] ++
      edgeSums d ++ [6*s-2,6*s+1] := by
    rw [join _ _ 0 0 nablast (head_append _ _ _ h.dh)]
    rw [join _ _ (3*s+2) (3*s+2) (last_append _ _ _ (by rfl)) (by rfl)]
    rw [join a _ (3*s-1) (3*s+1) h.lastA (by rfl)]
    rw [join _ b (3*s) (3*s-1) (by rfl) h.bh]
    rw [join d _ (3*s-2) (3*s) h.dt (by rfl)]
    simp only [edgeSums,List.append_assoc,List.cons_append,List.nil_append]
    have e1 : 3*s-1+(3*s+1)=6*s := by omega
    have e2 : 3*s+1+(3*s+2)=6*s+3 := by omega
    have e3 : 3*s+2+(3*s+2)=6*s+4 := by omega
    have e4 : 3*s+2+3*s=6*s+2 := by omega
    have e5 : 3*s+(3*s-1)=6*s-1 := by omega
    have e6 : 3*s-2+3*s=6*s-2 := by omega
    have e7 : 3*s+(3*s+1)=6*s+1 := by omega
    simp only [e1,e2,e3,e4,e5,e6,e7,Nat.zero_add]
  refine ⟨by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [List.length_append,h.la,List.length_cons,List.length_nil]; omega
  · simp only [List.length_append,h.lb,List.length_cons,List.length_nil]; omega
  · simp only [List.length_append,h.ld,List.length_cons,List.length_nil]; omega
  · exact head_append _ _ _ h.ah
  · have e : 3*(s+1)-1=3*s+2 := by omega
    rw [e]; exact last_append _ _ _ (by rfl)
  · simp only [List.cons_append,List.nil_append,List.head?_cons]; congr 1 <;> omega
  · exact last_append _ _ _ h.bt
  · exact head_append _ _ _ h.dh
  · have e : 3*(s+1)-2=3*s+1 := by omega
    rw [e]; exact last_append _ _ _ (by rfl)
  · apply List.perm_iff_count.mpr
    intro x
    have old := h.high.count_eq x
    simp only [highs_append,lows_append,ae,de,ab,nae,nab,ite_true,highs,lows,List.length_cons,List.length_nil,
      List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq] at old ⊢
    repeat (any_goals (first | omega | split at old | split))
  · apply List.perm_iff_count.mpr
    intro x
    have old := h.low.count_eq x
    simp only [highs_append,lows_append,ae,de,ab,nae,nab,ite_true,highs,lows,List.length_cons,List.length_nil,
      List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq] at old ⊢
    repeat (any_goals (first | omega | split at old | split))
  · apply List.perm_iff_count.mpr
    intro x
    have old := h.sums.count_eq x
    rw [oldedges] at old
    rw [newedges]
    simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq] at old ⊢
    repeat (any_goals (first | omega | split at old | split))

theorem triple_all (s : Nat) (hs : 1≤s) : Triple s (A s) (B s) (D s) := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases hz : s=0
    · subst s; constructor <;> decide
    · exact triple_step s _ _ _ (ih (by omega))

end GracefulBoundary.H1Concrete

