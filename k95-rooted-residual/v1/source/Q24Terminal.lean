import Q24B4Graft
namespace GracefulBoundary.Q24Terminal
open P20Q24

/- Exact B1/D23/A24 literal from the frozen author data.json. -/
def B : List Nat := [16]
def D : List Nat := [1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,9,9,11,21,24,24,23,23]
def A : List Nat := [14,15,15,10,12,16,10,13,8,11,13,14,17,17,18,18,19,19,20,20,22,22,21,12]
def surgery (u v : List Nat) := u.map (fun x => x+24) ++ B ++ [0,0] ++ D ++ v.map (fun x => x+24) ++ A
def extend (z : Nat) (c : List Nat) := surgery (c.take z) (c.drop (z+2))
def inserted := edgeSums (25::B++[0]) ++ edgeSums (0::D++[26]) ++ edgeSums (36::A)

theorem fresh_high : (highs D ++ lows A).Perm (List.range' 1 24) := by decide
theorem fresh_low : (highs B ++ lows D ++ highs A).Perm (List.range' 1 24) := by decide
theorem fresh_sums : inserted.Perm (List.range' 1 50) := by decide

set_option maxHeartbeats 2000000 in
theorem surgery_high (u v : List Nat) (hu : u.length%2=1) (hv : v.length%2=0)
    (hup : ∀ x∈u,0<x) (hvp : ∀ x∈v,0<x) :
    (highs (surgery u v)).Perm ((highs (u++[0,0]++v)).map bump24 ++ highs D ++ lows A) := by
  unfold surgery
  rw [← map_positive u hup,← map_positive v hvp]
  apply List.perm_iff_count.mpr
  intro x
  simp [List.append_assoc,highs_append,lows_append,highs_map,lows_map,hu,hv,B,D,A,bump24,highs,lows,List.count_cons,List.count_append]
  omega

set_option maxHeartbeats 2000000 in
theorem surgery_low (u v : List Nat) (hu : u.length%2=1) (hv : v.length%2=0)
    (hup : ∀ x∈u,0<x) (hvp : ∀ x∈v,0<x) :
    (lows (surgery u v)).Perm ((lows (u++[0,0]++v)).map bump24 ++ highs B ++ lows D ++ highs A) := by
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
  have a : ((highs c).map bump24 ++ highs D ++ lows A).Perm
      ((List.range (k+1)).map bump24 ++ List.range' 1 24) := by
    simpa only [List.append_assoc] using (h.high.map bump24).append fresh_high
  have b : ((lows c).map bump24 ++ highs B ++ lows D ++ highs A).Perm
      ((List.range k).map bump24 ++ List.range' 1 24) := by
    simpa only [List.append_assoc] using (h.low.map bump24).append fresh_low
  exact ⟨hh.trans (a.trans (side_interval (k+1) (by omega))),hl.trans (b.trans (side_interval k (by have := h.size; omega)))⟩

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
    Q24B4.edgeSums_shift24,Q24B4.edgeSums_shift24,List.map_append]
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
  have old := (Q24B4.old_sums (c.take z) (c.drop (z+2)) anchors.1 anchors.2.1).symm.trans
    (show (edgeSums (c.take z++[0,0]++c.drop (z+2))).Perm (List.range (2*k)) by rw [←decomposition k z c h]; exact h.sums)
  have next := (surgery_sums (c.take z) (c.drop (z+2)) anchors.1 anchors.2.1 anchors.2.2).trans
    (enlarged_sums (2*k) (by have := h.size; omega) _ old)
  simpa only [extend,show 2*k+48=2*(k+24) by omega] using next

theorem extend_length (k z : Nat) (c : List Nat) (h : State k z c) :
    (extend z c).length=2*(k+24)+1 := by
  have lens := part_lengths k z c h
  simp only [extend,surgery,List.length_append,List.length_map,lens.1,lens.2,B,D,A,
    List.length_cons,List.length_nil]
  have hi := h.zeroInside
  omega

theorem surgery_patch_index (u v : List Nat) (i : Nat) (hi : i<26) :
    (surgery u v)[u.length+i]?=(B++[0,0]++D)[i]? := by
  simp only [surgery,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map,show u.length+i-u.length=i by omega]
  rw [show B++([0,0]++(D++(v.map (fun x=>x+24)++A)))=
    (B++[0,0]++D)++(v.map (fun x=>x+24)++A) by simp only [List.append_assoc]]
  exact List.getElem?_append_left (by simpa only [B,D,List.length_append,List.length_cons,List.length_nil] using hi)

theorem extend_zeros (k z : Nat) (c : List Nat) (h : State k z c) :
    (extend z c)[z+1]?=some 0 ∧ (extend z c)[z+2]?=some 0 := by
  have lens := part_lengths k z c h
  have h1 := surgery_patch_index (c.take z) (c.drop (z+2)) 1 (by decide)
  have h2 := surgery_patch_index (c.take z) (c.drop (z+2)) 2 (by decide)
  simp only [lens.1] at h1 h2
  exact ⟨h1.trans (by rfl),h2.trans (by rfl)⟩

theorem surgery_right_index (u v : List Nat) (i : Nat) (hi : i<v.length) :
    (surgery u v)[u.length+26+i]?=v[i]?.map (fun x=>x+24) := by
  unfold surgery
  rw [show u.map (fun x=>x+24)++B++[0,0]++D++v.map (fun x=>x+24)++A=
    (u.map (fun x=>x+24)++B++[0,0]++D)++(v.map (fun x=>x+24)++A) by simp only [List.append_assoc]]
  have prefixLen : (u.map (fun x=>x+24)++B++[0,0]++D).length=u.length+26 := by
    simp only [List.length_map,List.length_append,B,D,List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by rw [prefixLen]; omega),prefixLen]
  rw [show u.length+26+i-(u.length+26)=i by omega]
  rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]

theorem extend_midpoint (k z : Nat) (c : List Nat) (h : State k z c) :
    (extend z c)[k+24]?=some (k+23) := by
  have hi := h.zeroInside
  have hs := h.size
  have lens := part_lengths k z c h
  have bound : k-(z+2)<(c.drop (z+2)).length := by rw [lens.2]; omega
  have look := surgery_right_index (c.take z) (c.drop (z+2)) (k-(z+2)) bound
  have old : (c.drop (z+2))[k-(z+2)]?=some (k-1) := by
    rw [List.getElem?_drop,show z+2+(k-(z+2))=k by omega]
    exact h.midpoint
  rw [lens.1,show z+26+(k-(z+2))=k+24 by omega,old] at look
  simpa only [extend,Option.map_some,show k-1+24=k+23 by omega] using look

/-- The terminal surgery is a valid alpha source for every old `State`, not just
    the P20 orbit. The H0/L0 extreme positions are tracked separately. -/
theorem generic_source (k z p : Nat) (c : List Nat) (h : State k z c)
    (hk : k=2*p+3) :
    GenericPathCertificate (p+12) (coreLabels (2*(k+24)) (extend z c)) ∧
    (coreLabels (2*(k+24)) (extend z c))[z+1]?=some (2*(k+24)) ∧
    (coreLabels (2*(k+24)) (extend z c))[z+2]?=some 0 := by
  have hlen : (extend z c).length=2*(k+24)+1 := extend_length k z c h
  have hsides := extend_sides k z c h
  have hsums := extend_sums k z c h
  have hmid := extend_midpoint k z c h
  have hz := extend_zeros k z c h
  have hc := WholeTagged.whole_path_certificate (p+12) (extend z c)
    (by simpa only [hk,show 2*(2*p+3+24)+1=2*(2*(p+12)+3)+1 by omega] using hlen)
    (by simpa only [hk,show 2*(p+12)+4=2*p+3+25 by omega] using hsides.1)
    (by simpa only [hk,show 2*(p+12)+3=2*p+3+24 by omega] using hsides.2)
    (by simpa only [hk,show 4*(p+12)+6=2*(2*p+3+24) by omega] using hsums)
    (by simpa only [hk,show 2*(p+12)+3=2*p+3+24 by omega,
      show 2*(p+12)+2=2*p+3+23 by omega] using hmid)
  have hM : 4*(p+12)+6=2*(k+24) := by omega
  rw [hM] at hc
  refine ⟨hc,?_,?_⟩
  · rw [coreLabels_lookup,hz.1]
    simp only [show (z+1)%2=0 by have := h.zeroOdd; omega,ite_true,Option.map_some,Nat.sub_zero]
  · rw [coreLabels_lookup,hz.2]
    simp only [show ¬(z+2)%2=0 by have := h.zeroOdd; omega,ite_false,Option.map_some]

def flipWord (s : Nat) : List Nat := extend (3+2*s) (P20Q24.word s)

theorem flip_certificate (s : Nat) :
    FiniteAlpha.Certificate (22+12*s) (42+22*s) (43+22*s)
      (coreLabels (94+48*s) (flipWord s)) := by
  have h := P20Q24.all_states s
  have lengthEq : 2*(22+12*s)+3=47+24*s := by omega
  have highEq : 2*(22+12*s)+4=47+24*s+1 := by omega
  have sumEq : 4*(22+12*s)+6=2*(47+24*s) := by omega
  have midEq : 2*(22+12*s)+2=47+24*s-1 := by omega
  have generic := WholeTagged.whole_path_certificate (22+12*s) (flipWord s)
    (by rw [lengthEq]; simpa only [flipWord,show 23+24*s+24=47+24*s by omega] using
      extend_length (23+24*s) (3+2*s) (P20Q24.word s) h)
    (by rw [highEq]; simpa only [flipWord,show 23+24*s+25=47+24*s+1 by omega] using
      (extend_sides (23+24*s) (3+2*s) (P20Q24.word s) h).1)
    (by rw [lengthEq]; simpa only [flipWord,show 23+24*s+24=47+24*s by omega] using
      (extend_sides (23+24*s) (3+2*s) (P20Q24.word s) h).2)
    (by rw [sumEq]; simpa only [flipWord,show 23+24*s+24=47+24*s by omega] using
      extend_sums (23+24*s) (3+2*s) (P20Q24.word s) h)
    (by rw [lengthEq,midEq]; simpa only [flipWord,show 23+24*s+24=47+24*s by omega,
      show 23+24*s+23=47+24*s-1 by omega] using
      extend_midpoint (23+24*s) (3+2*s) (P20Q24.word s) h)
  rw [show 4*(22+12*s)+6=94+48*s by omega] at generic
  refine ⟨by omega,by omega,by omega,by omega,generic,?_,?_⟩
  · rw [show 2*(22+12*s)+3-(42+22*s)=5+2*s by omega,coreLabels_lookup]
    rw [show 5+2*s=3+2*s+2 by omega]
    change Option.map (fun x => if (3+2*s+2)%2=0 then 94+48*s-x else x)
      (extend (3+2*s) (P20Q24.word s))[3+2*s+2]?=some 0
    rw [(extend_zeros (23+24*s) (3+2*s) (P20Q24.word s) h).2]
    simp only [show ¬(3+2*s+2)%2=0 by omega,ite_false,Option.map_some]
  · rw [show 2*(22+12*s)+3-(43+22*s)=4+2*s by omega,coreLabels_lookup]
    rw [show 4+2*s=3+2*s+1 by omega]
    change Option.map (fun x => if (3+2*s+1)%2=0 then 94+48*s-x else x)
      (extend (3+2*s) (P20Q24.word s))[3+2*s+1]?=some (4*(22+12*s)+6)
    rw [(extend_zeros (23+24*s) (3+2*s) (P20Q24.word s) h).1]
    simp only [show (3+2*s+1)%2=0 by omega,ite_true,Option.map_some,Nat.sub_zero]
    simp only [Nat.mul_add,←Nat.mul_assoc] at *
    simp only [show 4*22=88 by decide,show 4*12=48 by decide] at *
    congr 1
    omega

theorem flip_actual (s n m : Nat) (hn : 2≤n) (a : Fin n) :
    P20Q24.DepthZero n m (47+24*s) (42+22*s) a ∧
    P20Q24.DepthZero n m (47+24*s) (43+22*s) a := by
  have result := FiniteAlpha.prescribed_zero (22+12*s) (42+22*s) (43+22*s) n m
    (coreLabels (94+48*s) (flipWord s)) (flip_certificate s) hn a
  have hK : 2*(22+12*s)+3=47+24*s := by omega
  have lifted : P20Q24.DepthZero n m (2*(22+12*s)+3) (42+22*s) a ∧
      P20Q24.DepthZero n m (2*(22+12*s)+3) (43+22*s) a := by
    obtain ⟨f,hf,hz⟩ := result.1
    obtain ⟨g,hg,hm⟩ := result.2
    exact ⟨⟨by omega,f,hf,hz⟩,⟨by omega,g,hg,hm⟩⟩
  rw [hK] at lifted
  exact lifted

theorem terminal_actual (t n m : Nat) (ht : 1≤t) (hn : 2≤n) (a : Fin n) :
    P20Q24.DepthZero n m (23+24*t) (20+22*t) a ∧
    P20Q24.DepthZero n m (23+24*t) (21+22*t) a := by
  obtain ⟨s,rfl⟩ : ∃ s,t=s+1 := ⟨t-1,by omega⟩
  have h := flip_actual s n m hn a
  simpa only [show 23+24*(s+1)=47+24*s by omega,
    show 20+22*(s+1)=42+22*s by omega,
    show 21+22*(s+1)=43+22*s by omega] using h

end GracefulBoundary.Q24Terminal
