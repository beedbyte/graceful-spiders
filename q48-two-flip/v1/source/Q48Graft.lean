import Q24Family
namespace GracefulBoundary.Q48Flip
open P20Q24

def B : List Nat := [36,13]
def D : List Nat := [1,1,2,2,3,3,4,4,5,5,6,6,8,7,16,11,23,23,20,20,19,22,22,25,25,26,26,27,27,28,28,29,29,30,31,34,33,33,42,42,44,45,48,48,47,47]
def A : List Nat := [38,35,34,40,30,32,32,31,37,39,40,43,45,46,46,44,43,38,39,41,41,37,35,36,24,24,21,21,17,18,18,19,14,17,15,15,13,16,10,14,11,10,12,8,9,9,7,12]
def bump48 (x : Nat) : Nat := if x=0 then 0 else x+48
def surgery (u v : List Nat) := u.map (fun x => x+48) ++ B ++ [0,0] ++ D ++ v.map (fun x => x+48) ++ A
def extend (z : Nat) (c : List Nat) := surgery (c.take z) (c.drop (z+2))
def inserted := edgeSums (49::B++[0]) ++ edgeSums (0::D++[50]) ++ edgeSums (60::A)
theorem fresh_high : (lows B ++ lows D ++ lows A).Perm (List.range' 1 48) := by decide
theorem fresh_low : (highs B ++ highs D ++ highs A).Perm (List.range' 1 48) := by decide
theorem fresh_sums : inserted.Perm (List.range' 1 98) := by decide

theorem bump48_positive (x : Nat) (hx : 0<x) : bump48 x=x+48 := by simp [bump48,Nat.ne_of_gt hx]
theorem map_positive (c : List Nat) (hc : ∀ x∈c,0<x) : c.map bump48=c.map (fun x=>x+48) := by
  apply List.map_congr_left
  intro x hx
  exact bump48_positive x (hc x hx)

theorem side_interval (n : Nat) (hn : 1≤n) :
    ((List.range n).map bump48 ++ List.range' 1 48).Perm (List.range (n+48)) := by
  have hb : (List.range n).map bump48=0::List.range' 49 (n-1) := by
    obtain ⟨j,rfl⟩ : ∃ j,n=j+1 := ⟨n-1,by omega⟩
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map]
    have he : (fun x => bump48 (x+1))=(fun x=>49+x) := by
      funext x
      rw [bump48_positive _ (by omega)]
      omega
    change bump48 0 :: (List.range j).map (fun x=>bump48 (x+1)) = _
    rw [he]
    simp [bump48,List.range'_eq_map_range]
  rw [hb]
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_cons,count_band,List.count_range,Nat.beq_eq_true_eq]
  repeat (any_goals split)
  all_goals omega

set_option maxHeartbeats 2000000 in
theorem surgery_high (u v : List Nat) (hu : u.length%2=1) (hv : v.length%2=0)
    (hup : ∀ x∈u,0<x) (hvp : ∀ x∈v,0<x) :
    (highs (surgery u v)).Perm ((highs (u++[0,0]++v)).map bump48 ++ lows B ++ lows D ++ lows A) := by
  unfold surgery
  rw [← map_positive u hup,← map_positive v hvp]
  apply List.perm_iff_count.mpr
  intro x
  simp [List.append_assoc,highs_append,lows_append,highs_map,lows_map,hu,hv,B,D,A,bump48,highs,lows,List.count_cons,List.count_append]
  omega

set_option maxHeartbeats 2000000 in
theorem surgery_low (u v : List Nat) (hu : u.length%2=1) (hv : v.length%2=0)
    (hup : ∀ x∈u,0<x) (hvp : ∀ x∈v,0<x) :
    (lows (surgery u v)).Perm ((lows (u++[0,0]++v)).map bump48 ++ highs B ++ highs D ++ highs A) := by
  unfold surgery
  rw [← map_positive u hup,← map_positive v hvp]
  apply List.perm_iff_count.mpr
  intro x
  simp [List.append_assoc,highs_append,lows_append,highs_map,lows_map,hu,hv,B,D,A,bump48,highs,lows,List.count_cons,List.count_append]
  omega

theorem extend_sides (k z : Nat) (c : List Nat) (h : State k z c) :
    (highs (extend z c)).Perm (List.range (k+49)) ∧
    (lows (extend z c)).Perm (List.range (k+48)) := by
  have lens := part_lengths k z c h
  have hp := parts_positive k z c h
  have odd : (c.take z).length%2=1 := by rw [lens.1]; exact h.zeroOdd
  have even : (c.drop (z+2)).length%2=0 := by rw [lens.2]; have := h.zeroOdd; have := h.zeroInside; omega
  have hh := surgery_high (c.take z) (c.drop (z+2)) odd even hp.1 hp.2
  have hl := surgery_low (c.take z) (c.drop (z+2)) odd even hp.1 hp.2
  rw [← decomposition k z c h] at hh hl
  have a : ((highs c).map bump48 ++ lows B ++ lows D ++ lows A).Perm
      ((List.range (k+1)).map bump48 ++ List.range' 1 48) := by
    simpa only [List.append_assoc] using (h.high.map bump48).append fresh_high
  have b : ((lows c).map bump48 ++ highs B ++ highs D ++ highs A).Perm
      ((List.range k).map bump48 ++ List.range' 1 48) := by
    simpa only [List.append_assoc] using (h.low.map bump48).append fresh_low
  exact ⟨hh.trans (a.trans (side_interval (k+1) (by omega))),hl.trans (b.trans (side_interval k (by have := h.size; omega)))⟩

theorem edgeSums_shift48 (c : List Nat) :
    edgeSums (c.map (fun x=>x+48))=(edgeSums c).map (fun x=>x+96) := by
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
      ((edgeSums u ++ edgeSums v).map (fun x=>x+96) ++ [0] ++ inserted) := by
  have hulast : (u.map (fun x=>x+48)).getLast?=some 49 := by simp [List.getLast?_map,hu]
  have hvhead : (v.map (fun x=>x+48)++A).head?=some 50 := by simp [List.head?_append,List.head?_map,hv]
  have hvlast : (v.map (fun x=>x+48)).getLast?=some 60 := by simp [List.getLast?_map,he]
  unfold surgery
  rw [show u.map (fun x=>x+48)++B++[0,0]++D++v.map (fun x=>x+48)++A =
    u.map (fun x=>x+48)++(B++[0,0]++D++v.map (fun x=>x+48)++A) by simp only [List.append_assoc]]
  rw [Variable.edgeSums_left_last _ _ 49 hulast]
  rw [show 49::(B++[0,0]++D++v.map (fun x=>x+48)++A)=
    (49::B++[0,0]++D)++(v.map (fun x=>x+48)++A) by simp only [List.cons_append,List.append_assoc]]
  rw [Variable.edgeSums_right_head _ _ 50 hvhead,Variable.edgeSums_left_last _ A 60 hvlast,
    edgeSums_shift48,edgeSums_shift48,List.map_append]
  have middle : edgeSums ((49::B++[0,0]++D)++[50])=
    edgeSums (49::B++[0])++[0]++edgeSums (0::D++[50]) := by decide
  rw [middle]
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,inserted]
  omega

theorem enlarged_sums (N : Nat) (hN : 3≤N) (r : List Nat)
    (hr : ([0,1,2]++r).Perm (List.range N)) :
    (r.map (fun x=>x+96) ++ [0] ++ inserted).Perm (List.range (N+96)) := by
  have rest : r.Perm (List.range' 3 (N-3)) := by
    apply List.perm_iff_count.mpr
    intro x
    have h := hr.count_eq x
    simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq] at h
    simp only [count_band]
    repeat (any_goals (first | split at h | split))
    all_goals omega
  have shifted := rest.map (fun x=>x+96)
  have mapRange : (List.range' 3 (N-3)).map (fun x=>x+96)=List.range' 99 (N-3) := by
    have he : (fun x : Nat=>x+96)=(fun x=>96+x) := by funext x; omega
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
    (edgeSums (extend z c)).Perm (List.range (2*(k+48))) := by
  have anchors := part_anchors k z c h
  have old := (old_sums (c.take z) (c.drop (z+2)) anchors.1 anchors.2.1).symm.trans
    (show (edgeSums (c.take z++[0,0]++c.drop (z+2))).Perm (List.range (2*k)) by rw [←decomposition k z c h]; exact h.sums)
  have next := (surgery_sums (c.take z) (c.drop (z+2)) anchors.1 anchors.2.1 anchors.2.2).trans
    (enlarged_sums (2*k) (by have := h.size; omega) _ old)
  simpa only [extend,show 2*k+96=2*(k+48) by omega] using next

end GracefulBoundary.Q48Flip
