import Shell

namespace GracefulBoundary.LabelOne

structure Packet (r : Nat) (c : List Nat) : Prop where
  length : c.length=2*r+1
  low : (highs c).Perm (List.range r ++ [r+1])
  high : (lows c).Perm (List.range r)
  sums : (edgeSums c).Perm (List.range (2*r))
  first : c.head?=some (r+1)
  zero : c[2*r-2]?=some 0
  decodedZero : ∀ N,(decode N false c)[2*r-2]?=some 0

def base2 : List Nat := [3,0,0,1,1]
def base3 : List Nat := [4,1,2,2,0,0,1]
theorem base2_valid : Packet 2 base2 := by constructor <;> first | decide | (intro N; rfl)
theorem base3_valid : Packet 3 base3 := by constructor <;> first | decide | (intro N; rfl)

def step (r : Nat) (c : List Nat) : List Nat := [r+3,r,r,r+1]++c

theorem side_step (r : Nat) :
    ([r+3,r]++(List.range r++[r+1])).Perm (List.range (r+2)++[r+3]) ∧
    ([r,r+1]++List.range r).Perm (List.range (r+2)) := by
  constructor <;> apply List.perm_iff_count.mpr <;> intro x
  all_goals simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq]
  all_goals repeat (any_goals (first | omega | split))

theorem sum_step (r : Nat) :
    ([2*r+3,2*r,2*r+1,2*r+2]++List.range (2*r)).Perm (List.range (2*(r+2))) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq]
  repeat (any_goals (first | omega | split))

theorem step_valid (r : Nat) (hr : 2≤r) (c : List Nat) (hc : Packet r c) : Packet (r+2) (step r c) := by
  have hlo := (List.Perm.refl [r+3,r]).append hc.low
  have hhi := (List.Perm.refl [r,r+1]).append hc.high
  have hs : edgeSums (step r c)=[2*r+3,2*r,2*r+1,2*r+2]++edgeSums c := by
    obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp hc.first
    rw [eq]
    simp [step,edgeSums,Nat.add_comm,Nat.add_left_comm]
    omega
  refine ⟨by simp [step,hc.length]; omega,?_,?_,?_,by simp [step],?_,?_⟩
  · simpa only [step,highs,show highs ([r+3,r,r,r+1]++c)=[r+3,r]++highs c by rfl] using hlo.trans (side_step r).1
  · simpa only [step,lows,show lows ([r+3,r,r,r+1]++c)=[r,r+1]++lows c by rfl] using hhi.trans (side_step r).2
  · rw [hs]
    exact ((List.Perm.refl _).append hc.sums).trans (sum_step r)
  · have index : 2*(r+2)-2=4+(2*r-2) := by omega
    rw [step,index,List.getElem?_append_right (by simp)]
    simpa using hc.zero
  · intro N
    have index : 2*(r+2)-2=4+(2*r-2) := by omega
    change ([r+3,N-r,r,N-(r+1)]++decode N false c)[2*(r+2)-2]?=some 0
    rw [index,List.getElem?_append_right (by simp)]
    simpa using hc.decodedZero N

theorem packets : ∀ r,2≤r → ∃ c,Packet r c := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro hr
    by_cases two : r=2
    · subst r; exact ⟨base2,base2_valid⟩
    by_cases three : r=3
    · subst r; exact ⟨base3,base3_valid⟩
    obtain ⟨c,hc⟩ := ih (r-2) (by omega) (by omega)
    have next := step_valid (r-2) (by omega) c hc
    rw [show r-2+2=r by omega] at next
    exact ⟨step (r-2) c,next⟩

theorem decode_length (N : Nat) (b : Bool) (c : List Nat) : (decode N b c).length=c.length := by
  induction c generalizing b with
  | nil => rfl
  | cons a c ih => cases b <;> simp [decode,ih]

theorem decode_sums (N : Nat) (c : List Nat) (b : Bool) (hs : ∀ s∈edgeSums c,s≤N) :
    edgeDiffs (decode N b c)=(edgeSums c).map (fun s => N-s) := by
  induction c using edgeSums.induct generalizing b with
  | case1 => rfl
  | case2 a => cases b <;> rfl
  | case3 a x c ih =>
    have hax : a+x≤N := hs (a+x) (by simp [edgeSums])
    have ht : ∀ s∈edgeSums (x::c),s≤N := by intro s hm; exact hs s (by simp [edgeSums,hm])
    cases b with
    | false =>
      change distance a (N-x)::edgeDiffs (decode N true (x::c)) = _
      rw [ih true ht]
      simp only [edgeSums,List.map_cons]
      congr 1
      dsimp only [distance]
      omega
    | true =>
      change distance (N-a) x::edgeDiffs (decode N false (x::c)) = _
      rw [ih false ht]
      simp only [edgeSums,List.map_cons]
      congr 1
      dsimp only [distance]
      omega

theorem reverse_range_band (Q r : Nat) :
    ((List.range r).map (fun x => Q+2*r-x)).Perm (List.range' (Q+r+1) r) := by
  have he : (List.range' (Q+r+1) r).reverse=(List.range r).map (fun x => Q+2*r-x) := by
    rw [List.reverse_range']
    by_cases zero : r=0
    · subst r; rfl
    · have eq : Q+r+1+r-1=Q+2*r := by omega
      rw [eq]
  rw [←he]
  exact List.reverse_perm _

def armLabels (Q r : Nat) (c : List Nat) : List Nat := (decode (Q+2*r) false c).tail

theorem decoded_first (Q r : Nat) (c : List Nat) (hc : Packet r c) :
    decode (Q+2*r) false c=(r+1)::armLabels Q r c := by
  obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp hc.first
  simp [eq,decode,armLabels]

theorem arm_permutation (Q r : Nat) (c : List Nat) (hc : Packet r c) :
    (armLabels Q r c).Perm (List.range r++List.range' (Q+r+1) r) := by
  have whole := (decode_side_permutations (Q+2*r) c).2.trans
    (hc.low.append ((hc.high.map (fun x => Q+2*r-x)).trans (reverse_range_band Q r)))
  rw [decoded_first Q r c hc] at whole
  apply List.perm_iff_count.mpr
  intro x
  have ht := whole.count_eq x
  simp only [List.count_cons,List.count_append,List.count_nil] at ht ⊢
  omega

theorem arm_length (Q r : Nat) (c : List Nat) (hc : Packet r c) : (armLabels Q r c).length=2*r := by
  simp [armLabels,List.length_tail,decode_length,hc.length]

theorem arm_differences (Q r : Nat) (c : List Nat) (hc : Packet r c) :
    (edgeDiffs (decode (Q+2*r) false c)).Perm (List.range' (Q+1) (2*r)) := by
  have hb : ∀ s∈edgeSums c,s≤Q+2*r := by
    intro s hs
    have mem := hc.sums.mem_iff.mp hs
    simp only [List.mem_range] at mem
    omega
  rw [decode_sums (Q+2*r) c false hb]
  have he : (List.range' (Q+1) (2*r)).reverse=(List.range (2*r)).map (fun x => Q+2*r-x) := by
    rw [List.reverse_range']
    by_cases zero : r=0
    · subst r; rfl
    · rw [show Q+1+2*r-1=Q+2*r by omega]
  have perm := hc.sums.map (fun x => Q+2*r-x)
  rw [←he] at perm
  exact perm.trans (List.reverse_perm _)

end GracefulBoundary.LabelOne
