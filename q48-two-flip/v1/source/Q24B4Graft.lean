import Q24Family
namespace GracefulBoundary.Q24B4
open P20Q24

def B : List Nat := [24,21,20,1]
def D : List Nat := [2,3,1,2,4,6,7,9,10,13,11,15,17,19,18,20,19,23,21,22]
def A : List Nat := [14,11,9,8,6,5,3,4,5,7,8,10,12,16,15,14,13,17,16,18,22,24,23,12]
def surgery (u v : List Nat) := u.map (fun x => x+24) ++ B ++ [0,0] ++ D ++ v.map (fun x => x+24) ++ A
def extend (z : Nat) (c : List Nat) := surgery (c.take z) (c.drop (z+2))
def inserted := edgeSums (25::B++[0]) ++ edgeSums (0::D++[26]) ++ edgeSums (36::A)
theorem fresh_high : (lows B ++ lows D ++ lows A).Perm (List.range' 1 24) := by decide
theorem fresh_low : (highs B ++ highs D ++ highs A).Perm (List.range' 1 24) := by decide
theorem fresh_sums : inserted.Perm (List.range' 1 50) := by decide

set_option maxHeartbeats 2000000 in
theorem surgery_high (u v : List Nat) (hu : u.length%2=1) (hv : v.length%2=0)
    (hup : ∀ x∈u,0<x) (hvp : ∀ x∈v,0<x) :
    (highs (surgery u v)).Perm ((highs (u++[0,0]++v)).map bump24 ++ lows B ++ lows D ++ lows A) := by
  unfold surgery
  rw [← map_positive u hup,← map_positive v hvp]
  apply List.perm_iff_count.mpr
  intro x
  simp [List.append_assoc,highs_append,lows_append,highs_map,lows_map,hu,hv,B,D,A,bump24,highs,lows,List.count_cons,List.count_append]
  omega

set_option maxHeartbeats 2000000 in
theorem surgery_low (u v : List Nat) (hu : u.length%2=1) (hv : v.length%2=0)
    (hup : ∀ x∈u,0<x) (hvp : ∀ x∈v,0<x) :
    (lows (surgery u v)).Perm ((lows (u++[0,0]++v)).map bump24 ++ highs B ++ highs D ++ highs A) := by
  unfold surgery
  rw [← map_positive u hup,← map_positive v hvp]
  apply List.perm_iff_count.mpr
  intro x
  simp [List.append_assoc,highs_append,lows_append,highs_map,lows_map,hu,hv,B,D,A,bump24,highs,lows,List.count_cons,List.count_append]
  omega

theorem extend_sides (k z : Nat) (c : List Nat) (h : State k z c) :
    (highs (extend z c)).Perm (List.range (k+25)) ∧
    (lows (extend z c)).Perm (List.range (k+24)) := by
  have lens := part_lengths k z c h
  have hp := parts_positive k z c h
  have odd : (c.take z).length%2=1 := by rw [lens.1]; exact h.zeroOdd
  have even : (c.drop (z+2)).length%2=0 := by rw [lens.2]; have := h.zeroOdd; have := h.zeroInside; omega
  have hh := surgery_high (c.take z) (c.drop (z+2)) odd even hp.1 hp.2
  have hl := surgery_low (c.take z) (c.drop (z+2)) odd even hp.1 hp.2
  rw [← decomposition k z c h] at hh hl
  have a : ((highs c).map bump24 ++ lows B ++ lows D ++ lows A).Perm
      ((List.range (k+1)).map bump24 ++ List.range' 1 24) := by
    simpa only [List.append_assoc] using (h.high.map bump24).append fresh_high
  have b : ((lows c).map bump24 ++ highs B ++ highs D ++ highs A).Perm
      ((List.range k).map bump24 ++ List.range' 1 24) := by
    simpa only [List.append_assoc] using (h.low.map bump24).append fresh_low
  exact ⟨hh.trans (a.trans (side_interval (k+1) (by omega))),hl.trans (b.trans (side_interval k (by have := h.size; omega)))⟩

theorem edgeSums_shift24 (c : List Nat) :
    edgeSums (c.map (fun x=>x+24))=(edgeSums c).map (fun x=>x+48) := by
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
    (hv : v.head?=some 2) (he : v.getLast?=some 12) :
    (edgeSums (surgery u v)).Perm
      ((edgeSums u ++ edgeSums v).map (fun x=>x+48) ++ [0] ++ inserted) := by
  have hulast : (u.map (fun x=>x+24)).getLast?=some 25 := by simp [List.getLast?_map,hu]
  have hvhead : (v.map (fun x=>x+24)++A).head?=some 26 := by simp [List.head?_append,List.head?_map,hv]
  have hvlast : (v.map (fun x=>x+24)).getLast?=some 36 := by simp [List.getLast?_map,he]
  unfold surgery
  rw [show u.map (fun x=>x+24)++B++[0,0]++D++v.map (fun x=>x+24)++A =
    u.map (fun x=>x+24)++(B++[0,0]++D++v.map (fun x=>x+24)++A) by simp only [List.append_assoc]]
  rw [Variable.edgeSums_left_last _ _ 25 hulast]
  rw [show 25::(B++[0,0]++D++v.map (fun x=>x+24)++A)=
    (25::B++[0,0]++D)++(v.map (fun x=>x+24)++A) by simp only [List.cons_append,List.append_assoc]]
  rw [Variable.edgeSums_right_head _ _ 26 hvhead,Variable.edgeSums_left_last _ A 36 hvlast,
    edgeSums_shift24,edgeSums_shift24,List.map_append]
  have middle : edgeSums ((25::B++[0,0]++D)++[26])=
    edgeSums (25::B++[0])++[0]++edgeSums (0::D++[26]) := by decide
  rw [middle]
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,inserted]
  omega

theorem enlarged_sums (N : Nat) (hN : 3≤N) (r : List Nat)
    (hr : ([0,1,2]++r).Perm (List.range N)) :
    (r.map (fun x=>x+48) ++ [0] ++ inserted).Perm (List.range (N+48)) := by
  have rest : r.Perm (List.range' 3 (N-3)) := by
    apply List.perm_iff_count.mpr
    intro x
    have h := hr.count_eq x
    simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq] at h
    simp only [count_band]
    repeat (any_goals (first | split at h | split))
    all_goals omega
  have shifted := rest.map (fun x=>x+48)
  have mapRange : (List.range' 3 (N-3)).map (fun x=>x+48)=List.range' 51 (N-3) := by
    have he : (fun x : Nat=>x+48)=(fun x=>48+x) := by funext x; omega
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
    (edgeSums (extend z c)).Perm (List.range (2*(k+24))) := by
  have anchors := part_anchors k z c h
  have old := (old_sums (c.take z) (c.drop (z+2)) anchors.1 anchors.2.1).symm.trans
    (show (edgeSums (c.take z++[0,0]++c.drop (z+2))).Perm (List.range (2*k)) by rw [←decomposition k z c h]; exact h.sums)
  have next := (surgery_sums (c.take z) (c.drop (z+2)) anchors.1 anchors.2.1 anchors.2.2).trans
    (enlarged_sums (2*k) (by have := h.size; omega) _ old)
  simpa only [extend,show 2*k+48=2*(k+24) by omega] using next

end GracefulBoundary.Q24B4
