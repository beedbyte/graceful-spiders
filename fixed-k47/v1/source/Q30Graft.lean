import Q30Arrays
namespace GracefulBoundary.Q30

def bump30 (x : Nat) : Nat := if x=0 then 0 else x+30
def surgery (u v : List Nat) := u.map (fun x => x+30) ++ B ++ [0,0] ++ D ++ v.map (fun x => x+30) ++ A
def extend (z : Nat) (c : List Nat) := surgery (c.take z) (c.drop (z+2))
def inserted := edgeSums (31::B++[0]) ++ edgeSums (0::D++[32]) ++ edgeSums (46::A)

theorem fresh_high : (lows B ++ lows D ++ lows A).Perm (List.range' 1 30) := by decide
theorem fresh_low : (highs B ++ highs D ++ highs A).Perm (List.range' 1 30) := by decide
theorem fresh_sums : inserted.Perm (List.range' 1 62) := by decide

structure State (k z : Nat) (c : List Nat) : Prop where
  size : 17≤k
  odd : k%2=1
  zeroInside : 1≤z ∧ z+2<k
  zeroOdd : z%2=1
  length : c.length=2*k+1
  high : (highs c).Perm (List.range (k+1))
  low : (lows c).Perm (List.range k)
  sums : (edgeSums c).Perm (List.range (2*k))
  midpoint : c[k]?=some (k-1)
  neighbor1 : c[z-1]?=some 1
  lowZero : c[z]?=some 0
  highZero : c[z+1]?=some 0
  neighbor2 : c[z+2]?=some 2
  terminal : c[2*k]?=some 16

theorem decomposition (k z : Nat) (c : List Nat) (h : State k z c) :
    c=c.take z ++ [0,0] ++ c.drop (z+2) :=
  split_two c z 0 0 h.lowZero h.highZero

theorem part_lengths (k z : Nat) (c : List Nat) (h : State k z c) :
    (c.take z).length=z ∧ (c.drop (z+2)).length=2*k-z-1 := by
  simp only [List.length_take,List.length_drop,h.length]
  have hi := h.zeroInside
  omega

theorem parts_positive (k z : Nat) (c : List Nat) (h : State k z c) :
    (∀ x ∈ c.take z,0<x) ∧ (∀ x ∈ c.drop (z+2),0<x) := by
  have hh := h.high.count_eq 0
  have hl := h.low.count_eq 0
  simp only [List.count_range,show 0<k+1 by have := h.size; omega,
    show 0<k by have := h.size; omega,ite_true] at hh hl
  have ht := count_sides 0 c
  have hz : c.count 0=2 := by omega
  rw [decomposition k z c h] at hz
  simp only [List.count_append] at hz
  simp at hz
  have hu : (c.take z).count 0=0 := by omega
  have hv : (c.drop (z+2)).count 0=0 := by omega
  constructor
  · intro x hx
    have hn := List.not_mem_of_count_eq_zero hu
    by_cases he : x=0
    · subst x; exact False.elim (hn hx)
    · omega
  · intro x hx
    have hn := List.not_mem_of_count_eq_zero hv
    by_cases he : x=0
    · subst x; exact False.elim (hn hx)
    · omega

theorem part_anchors (k z : Nat) (c : List Nat) (h : State k z c) :
    (c.take z).getLast?=some 1 ∧ (c.drop (z+2)).head?=some 2 ∧
    (c.drop (z+2)).getLast?=some 16 := by
  have hz := h.zeroInside
  have nonempty : z≠0 := by omega
  have before : ¬c.length≤z+2 := by rw [h.length]; omega
  refine ⟨?_,?_,?_⟩
  · simp [List.getLast?_take,nonempty,h.neighbor1]
  · simpa using h.neighbor2
  · rw [List.getLast?_drop]
    simp only [before,ite_false]
    rw [List.getLast?_eq_getElem?,h.length,show 2*k+1-1=2*k by omega]
    exact h.terminal

theorem bump30_positive (x : Nat) (hx : 0<x) : bump30 x=x+30 := by simp [bump30,Nat.ne_of_gt hx]
theorem map_positive (c : List Nat) (hc : ∀ x∈c,0<x) : c.map bump30=c.map (fun x=>x+30) := by
  apply List.map_congr_left
  intro x hx
  exact bump30_positive x (hc x hx)

theorem side_interval (n : Nat) (hn : 1≤n) :
    ((List.range n).map bump30 ++ List.range' 1 30).Perm (List.range (n+30)) := by
  have hb : (List.range n).map bump30=0::List.range' 31 (n-1) := by
    obtain ⟨j,rfl⟩ : ∃ j,n=j+1 := ⟨n-1,by omega⟩
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map]
    have he : (fun x => bump30 (x+1))=(fun x=>31+x) := by
      funext x
      rw [bump30_positive _ (by omega)]
      omega
    change bump30 0 :: (List.range j).map (fun x=>bump30 (x+1)) = _
    rw [he]
    simp [bump30,List.range'_eq_map_range]
  rw [hb]
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_cons,count_band,List.count_range,Nat.beq_eq_true_eq]
  repeat (any_goals split)
  all_goals omega

set_option maxHeartbeats 2000000 in
theorem surgery_high (u v : List Nat) (hu : u.length%2=1) (hv : v.length%2=0)
    (hup : ∀ x∈u,0<x) (hvp : ∀ x∈v,0<x) :
    (highs (surgery u v)).Perm ((highs (u++[0,0]++v)).map bump30 ++ lows B ++ lows D ++ lows A) := by
  unfold surgery
  rw [← map_positive u hup,← map_positive v hvp]
  apply List.perm_iff_count.mpr
  intro x
  simp [List.append_assoc,highs_append,lows_append,highs_map,lows_map,hu,hv,B,D,A,bump30,highs,lows,List.count_cons,List.count_append]
  omega

set_option maxHeartbeats 2000000 in
theorem surgery_low (u v : List Nat) (hu : u.length%2=1) (hv : v.length%2=0)
    (hup : ∀ x∈u,0<x) (hvp : ∀ x∈v,0<x) :
    (lows (surgery u v)).Perm ((lows (u++[0,0]++v)).map bump30 ++ highs B ++ highs D ++ highs A) := by
  unfold surgery
  rw [← map_positive u hup,← map_positive v hvp]
  apply List.perm_iff_count.mpr
  intro x
  simp [List.append_assoc,highs_append,lows_append,highs_map,lows_map,hu,hv,B,D,A,bump30,highs,lows,List.count_cons,List.count_append]
  omega

theorem extend_sides (k z : Nat) (c : List Nat) (h : State k z c) :
    (highs (extend z c)).Perm (List.range (k+31)) ∧
    (lows (extend z c)).Perm (List.range (k+30)) := by
  have lens := part_lengths k z c h
  have hp := parts_positive k z c h
  have odd : (c.take z).length%2=1 := by rw [lens.1]; exact h.zeroOdd
  have even : (c.drop (z+2)).length%2=0 := by rw [lens.2]; have := h.zeroOdd; have := h.zeroInside; omega
  have hh := surgery_high (c.take z) (c.drop (z+2)) odd even hp.1 hp.2
  have hl := surgery_low (c.take z) (c.drop (z+2)) odd even hp.1 hp.2
  rw [← decomposition k z c h] at hh hl
  have a : ((highs c).map bump30 ++ lows B ++ lows D ++ lows A).Perm
      ((List.range (k+1)).map bump30 ++ List.range' 1 30) := by
    simpa only [List.append_assoc] using (h.high.map bump30).append fresh_high
  have b : ((lows c).map bump30 ++ highs B ++ highs D ++ highs A).Perm
      ((List.range k).map bump30 ++ List.range' 1 30) := by
    simpa only [List.append_assoc] using (h.low.map bump30).append fresh_low
  exact ⟨hh.trans (a.trans (side_interval (k+1) (by omega))),hl.trans (b.trans (side_interval k (by have := h.size; omega)))⟩

theorem edgeSums_shift30 (c : List Nat) :
    edgeSums (c.map (fun x=>x+30))=(edgeSums c).map (fun x=>x+60) := by
  induction c using edgeSums.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b xs ih =>
    simp only [List.map_cons,edgeSums]
    congr 1
    omega

theorem old_sums (u v : List Nat) (hu : u.getLast?=some 1) (hv : v.head?=some 2) :
    (edgeSums (u++[0,0]++v)).Perm ([0,1,2] ++ (edgeSums u ++ edgeSums v)) := by
  rw [show u++[0,0]++v=u++([0,0]++v) by simp only [List.append_assoc],Variable.edgeSums_left_last u _ 1 hu]
  rw [show 1::([0,0]++v)=[1,0,0]++v by rfl,Variable.edgeSums_right_head _ v 2 hv]
  apply List.perm_iff_count.mpr
  intro x
  simp [edgeSums,List.count_append,List.count_cons]
  omega

theorem surgery_sums (u v : List Nat) (hu : u.getLast?=some 1)
    (hv : v.head?=some 2) (he : v.getLast?=some 16) :
    (edgeSums (surgery u v)).Perm
      ((edgeSums u ++ edgeSums v).map (fun x=>x+60) ++ [0] ++ inserted) := by
  have hulast : (u.map (fun x=>x+30)).getLast?=some 31 := by simp [List.getLast?_map,hu]
  have hvhead : (v.map (fun x=>x+30)++A).head?=some 32 := by simp [List.head?_append,List.head?_map,hv]
  have hvlast : (v.map (fun x=>x+30)).getLast?=some 46 := by simp [List.getLast?_map,he]
  unfold surgery
  rw [show u.map (fun x=>x+30)++B++[0,0]++D++v.map (fun x=>x+30)++A =
    u.map (fun x=>x+30)++(B++[0,0]++D++v.map (fun x=>x+30)++A) by simp only [List.append_assoc]]
  rw [Variable.edgeSums_left_last _ _ 31 hulast]
  rw [show 31::(B++[0,0]++D++v.map (fun x=>x+30)++A)=
    (31::B++[0,0]++D)++(v.map (fun x=>x+30)++A) by simp only [List.cons_append,List.append_assoc]]
  rw [Variable.edgeSums_right_head _ _ 32 hvhead,Variable.edgeSums_left_last _ A 46 hvlast,
    edgeSums_shift30,edgeSums_shift30,List.map_append]
  have middle : edgeSums ((31::B++[0,0]++D)++[32])=
    edgeSums (31::B++[0])++[0]++edgeSums (0::D++[32]) := by decide
  rw [middle]
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,inserted]
  omega

theorem enlarged_sums (N : Nat) (hN : 3≤N) (r : List Nat)
    (hr : ([0,1,2]++r).Perm (List.range N)) :
    (r.map (fun x=>x+60) ++ [0] ++ inserted).Perm (List.range (N+60)) := by
  have rest : r.Perm (List.range' 3 (N-3)) := by
    apply List.perm_iff_count.mpr
    intro x
    have h := hr.count_eq x
    simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq] at h
    simp only [count_band]
    repeat (any_goals (first | split at h | split))
    all_goals omega
  have shifted := rest.map (fun x=>x+60)
  have mapRange : (List.range' 3 (N-3)).map (fun x=>x+60)=List.range' 63 (N-3) := by
    have he : (fun x : Nat=>x+60)=(fun x=>60+x) := by funext x; omega
    rw [he,List.map_add_range']
  rw [mapRange] at shifted
  apply List.perm_iff_count.mpr
  intro x
  have h := shifted.count_eq x
  have fresh := fresh_sums.count_eq x
  simp only [count_band] at h fresh
  simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq]
  rw [h,fresh]
  repeat (any_goals split)
  all_goals omega

theorem extend_sums (k z : Nat) (c : List Nat) (h : State k z c) :
    (edgeSums (extend z c)).Perm (List.range (2*(k+30))) := by
  have anchors := part_anchors k z c h
  have old := (old_sums (c.take z) (c.drop (z+2)) anchors.1 anchors.2.1).symm.trans
    (show (edgeSums (c.take z++[0,0]++c.drop (z+2))).Perm (List.range (2*k)) by rw [←decomposition k z c h]; exact h.sums)
  have next := (surgery_sums (c.take z) (c.drop (z+2)) anchors.1 anchors.2.1 anchors.2.2).trans
    (enlarged_sums (2*k) (by have := h.size; omega) _ old)
  simpa only [extend,show 2*k+60=2*(k+30) by omega] using next

end GracefulBoundary.Q30
