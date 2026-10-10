import EvenAttachment

namespace GracefulBoundary.OddNearTip
open LabelOne

structure Packet (r : Nat) (c : List Nat) : Prop where
  length : c.length=2*r+2
  high : (highs c).Perm (List.range r++[r+1])
  low : (lows c).Perm (List.range (r+1))
  sums : (edgeSums c).Perm (List.range (2*r+1))
  first : c.head?=some (r+1)
  decodedZero : ∀ N,(decode N true c)[2*r-1]?=some 0

def base3 : List Nat := [4,2,2,3,0,0,1,1]
def base4 : List Nat := [5,3,3,4,1,2,2,0,0,1]
theorem base3_valid : Packet 3 base3 := by constructor <;> first | decide | (intro N; rfl)
theorem base4_valid : Packet 4 base4 := by constructor <;> first | decide | (intro N; rfl)

def step (r : Nat) (c : List Nat) : List Nat := [r+3,r+1,r,r+2]++c

theorem sum_step (r : Nat) :
    ([2*r+4,2*r+1,2*r+2,2*r+3]++List.range (2*r+1)).Perm (List.range (2*(r+2)+1)) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq]
  repeat (any_goals (first | omega | split))

theorem step_valid (r : Nat) (hr : 3≤r) (c : List Nat) (hc : Packet r c) : Packet (r+2) (step r c) := by
  have hhi := (List.Perm.refl [r+3,r]).append hc.high
  have hlo := (List.Perm.refl [r+1,r+2]).append hc.low
  have lower : ([r+1,r+2]++List.range (r+1)).Perm (List.range (r+3)) := by
    simpa only [show r+1+1=r+2 by omega,show r+1+2=r+3 by omega] using (LabelOne.side_step (r+1)).2
  have hs : edgeSums (step r c)=[2*r+4,2*r+1,2*r+2,2*r+3]++edgeSums c := by
    obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp hc.first
    rw [eq]
    simp [step,edgeSums]
    omega
  refine ⟨by simp [step,hc.length]; omega,?_,?_,?_,by simp [step],?_⟩
  · exact hhi.trans (LabelOne.side_step r).1
  · exact hlo.trans lower
  · rw [hs]
    exact ((List.Perm.refl _).append hc.sums).trans (sum_step r)
  · intro N
    have index : 2*(r+2)-1=4+(2*r-1) := by omega
    change ([N-(r+3),r+1,N-r,r+2]++decode N true c)[2*(r+2)-1]?=some 0
    rw [index,List.getElem?_append_right (by simp)]
    simpa using hc.decodedZero N

theorem packets : ∀ r,3≤r → ∃ c,Packet r c := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro hr
    by_cases three : r=3
    · subst r; exact ⟨base3,base3_valid⟩
    by_cases four : r=4
    · subst r; exact ⟨base4,base4_valid⟩
    obtain ⟨c,hc⟩ := ih (r-2) (by omega) (by omega)
    have next := step_valid (r-2) (by omega) c hc
    rw [show r-2+2=r by omega] at next
    exact ⟨step (r-2) c,next⟩

def armLabels (Q r : Nat) (c : List Nat) : List Nat := (decode (Q+2*r+1) true c).tail

theorem decoded_first (Q r : Nat) (c : List Nat) (hc : Packet r c) :
    decode (Q+2*r+1) true c=(Q+r)::armLabels Q r c := by
  obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp hc.first
  have root : Q+2*r+1-(r+1)=Q+r := by omega
  simp only [eq,decode,root,armLabels,List.tail_cons,ite_true]

theorem high_band (Q r : Nat) :
    ((List.range r).map (fun x => Q+2*r+1-x)).Perm (List.range' (Q+r+2) r) := by
  have perm := LabelOne.reverse_range_band (Q+1) r
  rw [show Q+1+2*r=Q+2*r+1 by omega,show Q+1+r+1=Q+r+2 by omega] at perm
  exact perm

theorem arm_permutation (Q r : Nat) (c : List Nat) (hc : Packet r c) :
    (armLabels Q r c).Perm (List.range (r+1)++List.range' (Q+r+2) r) := by
  have root : Q+2*r+1-(r+1)=Q+r := by omega
  have whole := (decode_side_permutations (Q+2*r+1) c).1.trans
    ((hc.high.map (fun x => Q+2*r+1-x)).append hc.low)
  simp only [List.map_append,List.map_cons,List.map_nil,root] at whole
  rw [decoded_first Q r c hc] at whole
  apply List.perm_iff_count.mpr
  intro x
  have ht := whole.count_eq x
  have hm := (high_band Q r).count_eq x
  simp only [List.count_append,List.count_cons,List.count_nil] at ht ⊢
  omega

theorem arm_length (Q r : Nat) (c : List Nat) (hc : Packet r c) : (armLabels Q r c).length=2*r+1 := by
  simp [armLabels,List.length_tail,LabelOne.decode_length,hc.length]

theorem arm_differences (Q r : Nat) (c : List Nat) (hc : Packet r c) :
    (edgeDiffs (decode (Q+2*r+1) true c)).Perm (List.range' (Q+1) (2*r+1)) := by
  have hb : ∀ s∈edgeSums c,s≤Q+2*r+1 := by
    intro s hs
    have mem := hc.sums.mem_iff.mp hs
    simp only [List.mem_range] at mem
    omega
  rw [LabelOne.decode_sums (Q+2*r+1) c true hb]
  have he : (List.range' (Q+1) (2*r+1)).reverse=(List.range (2*r+1)).map (fun x => Q+2*r+1-x) := by
    rw [List.reverse_range',show Q+1+(2*r+1)-1=Q+2*r+1 by omega]
  have perm := hc.sums.map (fun x => Q+2*r+1-x)
  rw [←he] at perm
  exact perm.trans (List.reverse_perm _)

end GracefulBoundary.OddNearTip
