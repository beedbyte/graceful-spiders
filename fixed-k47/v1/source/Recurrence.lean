import Interfaces
namespace GracefulBoundary

theorem sides_cons (c : List Nat) : ∀ a,
    highs (a::c)=a::lows c ∧ lows (a::c)=highs c := by
  induction c with
  | nil => intro a; exact ⟨rfl,rfl⟩
  | cons b c ih =>
    intro a
    change a::highs c = a::lows (b::c) ∧ b::lows c = highs (b::c)
    exact ⟨congrArg (List.cons a) (ih b).2.symm, (ih b).1.symm⟩

@[simp] theorem highs_cons (a : Nat) (c : List Nat) : highs (a::c)=a::lows c :=
  (sides_cons c a).1
@[simp] theorem lows_cons (a : Nat) (c : List Nat) : lows (a::c)=highs c :=
  (sides_cons c a).2
theorem sides_append (u v : List Nat) :
    highs (u++v)=highs u ++ (if u.length%2=0 then highs v else lows v) ∧
    lows (u++v)=lows u ++ (if u.length%2=0 then lows v else highs v) := by
  induction u with
  | nil => simp [highs, lows]
  | cons a u ih =>
    by_cases he : u.length%2=0
    · have ho : ¬ (u.length+1)%2=0 := by omega
      simp [List.cons_append, ih.1, ih.2, he, ho]
    · have ho : (u.length+1)%2=0 := by omega
      simp [List.cons_append, ih.1, ih.2, he, ho]

theorem sides_map (f : Nat → Nat) (c : List Nat) :
    highs (c.map f)=(highs c).map f ∧ lows (c.map f)=(lows c).map f := by
  induction c with
  | nil => simp [highs,lows]
  | cons a c ih => simp [ih.1,ih.2]

theorem count_sides (x : Nat) (c : List Nat) :
    (highs c).count x + (lows c).count x = c.count x := by
  induction c with
  | nil => rfl
  | cons a c ih => simp only [highs_cons,lows_cons,List.count_cons]; omega

theorem core_zero_count (s : Nat) (c : List Nat) (hc : CoreInvariant s c) : c.count 0=2 := by
  rcases hc with ⟨hs,_,hh,hl,_⟩
  have hhigh := hh.count_eq 0
  have hlow := hl.count_eq 0
  have hp : 0 < 3*s := by omega
  simp only [List.count_range, hp, ite_true] at hhigh hlow
  have ht := count_sides 0 c
  omega

/-- Exact decomposition at two consecutive known values. -/
theorem split_two (c : List Nat) (i a b : Nat) (ha : c[i]?=some a) (hb : c[i+1]?=some b) :
    c = c.take i ++ [a,b] ++ c.drop (i+2) := by
  obtain ⟨hlen0,ea⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hlen,eb⟩ := List.getElem?_eq_some_iff.mp hb
  have hd := List.drop_eq_getElem_cons hlen0
  have hd1 := List.drop_eq_getElem_cons hlen
  have hcat := List.take_append_drop i c
  rw [hd,hd1,ea,eb] at hcat
  simpa [List.append_assoc] using hcat.symm

/-- Outside the anchored zero pair, every entry is nonzero. -/
theorem core_parts_positive (s : Nat) (c : List Nat) (hc : CoreInvariant s c) :
    (∀ x ∈ c.take (4*s-1), 0 < x) ∧ (∀ x ∈ c.drop (4*s+1), 0 < x) := by
  have hs := hc.1
  have hcount := core_zero_count s c hc
  obtain ⟨_,_,_,_,_,_,_,_,hz,hz',_⟩ := hc
  have hzindex : 4*s-1+1=4*s := by omega
  have hzindex' : 4*s-1+2=4*s+1 := by omega
  have hd := split_two c (4*s-1) 0 0 hz (by simpa [hzindex] using hz')
  rw [hzindex'] at hd
  rw [hd] at hcount
  simp only [List.count_append] at hcount
  simp at hcount
  have hu : (c.take (4*s-1)).count 0=0 := by omega
  have hv : (c.drop (4*s+1)).count 0=0 := by omega
  constructor
  · intro x hx
    have hn := List.not_mem_of_count_eq_zero hu
    by_cases h : x=0
    · subst x; exact False.elim (hn hx)
    · omega
  · intro x hx
    have hn := List.not_mem_of_count_eq_zero hv
    by_cases h : x=0
    · subst x; exact False.elim (hn hx)
    · omega

theorem map_bump_of_positive (c : List Nat) (h : ∀ x ∈ c, 0 < x) :
    c.map bump=c.map (fun x => x+6) := by
  apply List.map_congr_left
  intro x hx
  exact bump_positive x (h x hx)


theorem highs_append (u v : List Nat) :
    highs (u++v)=highs u ++ (if u.length%2=0 then highs v else lows v) := (sides_append u v).1

theorem lows_append (u v : List Nat) :
    lows (u++v)=lows u ++ (if u.length%2=0 then lows v else highs v) := (sides_append u v).2

theorem highs_map (f : Nat → Nat) (c : List Nat) : highs (c.map f)=(highs c).map f :=
  (sides_map f c).1

theorem lows_map (f : Nat → Nat) (c : List Nat) : lows (c.map f)=(lows c).map f :=
  (sides_map f c).2

def surgery (u v : List Nat) :=
  [3,5,6,3,2,4] ++ u.map bump ++ [6,4,0,0,1,1,2,5] ++ v.map bump

theorem surgery_highs (u v : List Nat) (hu : u.length%2=1) :
    (highs (surgery u v)).Perm ((highs (u++[0,0]++v)).map bump ++ [3,6,2,4,1,5]) := by
  apply List.perm_iff_count.mpr
  intro x
  simp [surgery, List.append_assoc, highs_append,highs_map,lows_map,hu,
    lows,bump,List.count_cons]
  omega

theorem surgery_lows (u v : List Nat) (hu : u.length%2=1) :
    (lows (surgery u v)).Perm ((lows (u++[0,0]++v)).map bump ++ [5,3,4,6,1,2]) := by
  apply List.perm_iff_count.mpr
  intro x
  simp [surgery, List.append_assoc, lows_append,highs_map,lows_map,hu,
    highs,bump,List.count_cons]
  omega

/-- Mapping all old side labels and adjoining the six new labels gives
    the complete enlarged interval, with exact multiplicities. -/
theorem bump_range (p : Nat) (hp : 1 ≤ p) :
    (List.range p).map bump = 0 :: List.range' 7 (p-1) := by
  obtain ⟨n,hn⟩ : ∃ n, p=n+1 := ⟨p-1,by omega⟩
  subst p
  rw [List.range_succ_eq_map]
  simp only [List.map_cons,List.map_map]
  have hf : (fun x => bump (x+1)) = (fun x => 7+x) := by
    funext x
    rw [bump_positive _ (by omega)]
    omega
  change bump 0 :: (List.range n).map (fun x => bump (x+1)) = _
  rw [hf]
  simp [bump, List.range'_eq_map_range]

theorem side_interval_extension (p : Nat) (hp : 1 ≤ p) :
    ((List.range p).map bump ++ List.range' 1 6).Perm (List.range (p+6)) := by
  rw [bump_range p hp]
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_cons,count_band,List.count_range]
  simp only [Nat.beq_eq_true_eq]
  repeat (any_goals split)
  all_goals omega

theorem extend_side_partitions (s : Nat) (c : List Nat) (hc : CoreInvariant s c) :
    (highs (extend s c)).Perm (List.range (3*(s+2))) ∧
    (lows (extend s c)).Perm (List.range (3*(s+2))) := by
  have hs := hc.1
  rcases hc with ⟨_,hlen,hh,hl,_,_,_,_,hz,hz',_⟩
  have hd := split_two c (4*s-1) 0 0 hz (by simpa [show 4*s-1+1=4*s by omega] using hz')
  rw [show 4*s-1+2=4*s+1 by omega] at hd
  have hu : (c.take (4*s-1)).length%2=1 := by
    simp only [List.length_take,hlen]; omega
  have eh := surgery_highs (c.take (4*s-1)) (c.drop (4*s+1)) hu
  have el := surgery_lows (c.take (4*s-1)) (c.drop (4*s+1)) hu
  rw [← hd] at eh el
  have hmhigh := (List.Perm.map bump hh).append high_gadget
  have hmlow := (List.Perm.map bump hl).append low_gadget
  have hp := side_interval_extension (3*s) (by omega)
  have ht : 3*s+6=3*(s+2) := by omega
  constructor
  · simpa only [surgery,extend,ht] using eh.trans (hmhigh.trans hp)
  · simpa only [surgery,extend,ht] using el.trans (hmlow.trans hp)

theorem edgeSums_overlap (u : List Nat) (a : Nat) (v : List Nat) :
    edgeSums (u++a::v)=edgeSums (u++[a]) ++ edgeSums (a::v) := by
  induction u with
  | nil => simp [edgeSums]
  | cons b u ih =>
    cases u with
    | nil => simp [edgeSums]
    | cons d u => simpa only [List.cons_append,edgeSums,List.cons_append] using congrArg (List.cons (b+d)) ih

theorem edgeSums_join (u : List Nat) (a b : Nat) (v : List Nat) (hu : u.getLast?=some a) :
    edgeSums (u++b::v)=edgeSums u ++ (a+b)::edgeSums (b::v) := by
  induction u with
  | nil => simp at hu
  | cons x u ih =>
    cases u with
    | nil => simp at hu; subst x; rfl
    | cons y u =>
      have ht : (y::u).getLast?=some a := by simpa using hu
      simpa only [List.cons_append,edgeSums,List.cons_append] using congrArg (List.cons (x+y)) (ih ht)

theorem edgeSums_shift (c : List Nat) :
    edgeSums (c.map (fun x => x+6))=(edgeSums c).map (fun x => x+12) := by
  induction c using edgeSums.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b xs ih =>
    simp only [List.map_cons,edgeSums]
    congr 1
    omega

theorem surgery_sums (u v : List Nat)
    (hu0 : u.head?=some 3) (hu4 : u.getLast?=some 4) (hv1 : v.head?=some 1)
    (hup : ∀ x ∈ u, 0 < x) (hvp : ∀ x ∈ v, 0 < x) :
    (edgeSums (surgery u v)).Perm
      ((edgeSums u ++ edgeSums v).map (fun x => x+12) ++ [0] ++ insertedSums) := by
  rw [surgery, map_bump_of_positive u hup, map_bump_of_positive v hvp]
  obtain ⟨ut,hut⟩ := List.head?_eq_some_iff.mp hu0
  obtain ⟨vt,hvt⟩ := List.head?_eq_some_iff.mp hv1
  have hum : (u.map (fun x => x+6)).getLast?=some 10 := by
    simp [List.getLast?_map,hu4]
  have houter :
      edgeSums ([3,5,6,3,2,4] ++ u.map (fun x => x+6) ++
        [6,4,0,0,1,1,2,5] ++ v.map (fun x => x+6)) =
      [8,11,9,5,6,13] ++ edgeSums (u.map (fun x => x+6) ++
        [6,4,0,0,1,1,2,5] ++ v.map (fun x => x+6)) := by
    rw [hut]
    rfl
  rw [houter]
  have hinner : edgeSums (u.map (fun x => x+6) ++
        [6,4,0,0,1,1,2,5] ++ v.map (fun x => x+6)) =
      edgeSums (u.map (fun x => x+6)) ++
        [16,10,4,0,1,2,3,7,12] ++ edgeSums (v.map (fun x => x+6)) := by
    rw [List.append_assoc]
    change edgeSums (u.map (fun x => x+6) ++ 6::(4::0::0::1::1::2::5::v.map (fun x => x+6))) = _
    rw [edgeSums_join _ 10 6 _ hum, hvt]
    simp [edgeSums,List.append_assoc]
  rw [hinner,edgeSums_shift,edgeSums_shift,List.map_append]
  apply List.perm_iff_count.mpr
  intro x
  simp [insertedSums,List.count_cons]
  omega

theorem old_sums (u v : List Nat) (hu : u.getLast?=some 4) (hv : v.head?=some 1) :
    (edgeSums (u++[0,0]++v)).Perm ([0,1,4] ++ (edgeSums u ++ edgeSums v)) := by
  obtain ⟨vs,hvs⟩ := List.head?_eq_some_iff.mp hv
  rw [List.append_assoc]
  change (edgeSums (u++0::0::v)).Perm _
  rw [edgeSums_join u 4 0 (0::v) hu,hvs]
  apply List.perm_iff_count.mpr
  intro x
  simp [edgeSums,List.count_cons]
  omega

set_option maxHeartbeats 1000000 in
theorem remove_three_sum_values (N : Nat) (hN : 5 ≤ N) (r : List Nat)
    (hr : ([0,1,4]++r).Perm (List.range N)) :
    r.Perm ([2,3]++List.range' 5 (N-5)) := by
  apply List.perm_iff_count.mpr
  intro x
  have hc := hr.count_eq x
  simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,count_band,Nat.beq_eq_true_eq] at hc ⊢
  repeat (any_goals split at hc)
  repeat (any_goals split)
  all_goals omega

theorem shifted_rest_interval (N : Nat) (hN : 5 ≤ N) (r : List Nat)
    (hr : ([0,1,4]++r).Perm (List.range N)) :
    (r.map (fun x => x+12)).Perm ([14,15]++List.range' 17 (N-5)) := by
  have h := List.Perm.map (fun x => x+12) (remove_three_sum_values N hN r hr)
  have hf : (fun x : Nat => x+12) = (fun x => 12+x) := by funext x; omega
  have hrange : (List.range' 5 (N-5)).map (fun x => x+12)=List.range' 17 (N-5) := by
    rw [hf,List.map_add_range']
  simpa only [List.map_append,List.map_cons,List.map_nil,hrange] using h

set_option maxHeartbeats 1000000 in
theorem enlarged_sum_interval (N : Nat) (hN : 5 ≤ N) (r : List Nat)
    (hr : ([0,1,4]++r).Perm (List.range N)) :
    (r.map (fun x => x+12) ++ [0] ++ insertedSums).Perm (List.range (N+12)) := by
  have hm := shifted_rest_interval N hN r hr
  apply List.perm_iff_count.mpr
  intro x
  have hc := hm.count_eq x
  have hi := inserted_sums_exact.count_eq x
  simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,count_band,Nat.beq_eq_true_eq] at hc hi ⊢
  rw [hc,hi]
  repeat (any_goals split)
  all_goals omega

theorem core_part_boundaries (s : Nat) (c : List Nat) (hc : CoreInvariant s c) :
    (c.take (4*s-1)).head?=some 3 ∧
    (c.take (4*s-1)).getLast?=some 4 ∧
    (c.drop (4*s+1)).head?=some 1 ∧
    (c.drop (4*s+1)).getLast?=some (3*s-4) := by
  rcases hc with ⟨hs,hlen,_,_,_,hf,ht,hn,_,_,hv⟩
  have hnz : 4*s-1 ≠ 0 := by omega
  have hi : 4*s-1-1=4*s-2 := by omega
  have hshort : ¬ c.length ≤ 4*s+1 := by omega
  refine ⟨?_,?_,?_,?_⟩
  · rw [List.head?_eq_getElem?,List.getElem?_take_of_lt (by omega)]
    exact hf
  · simp [List.getLast?_take,hnz,hi,hn]
  · simpa using hv
  · rw [List.getLast?_drop]
    simp only [hshort,ite_false]
    rw [List.getLast?_eq_getElem?,hlen]
    exact ht

theorem extend_edge_partition (s : Nat) (c : List Nat) (hc : CoreInvariant s c) :
    (edgeSums (extend s c)).Perm (List.range (6*(s+2)-1)) := by
  have hs := hc.1
  have hb := core_part_boundaries s c hc
  have hpos := core_parts_positive s c hc
  rcases hc with ⟨_,_,_,_,he,_,_,_,hz,hz',_⟩
  have hd := split_two c (4*s-1) 0 0 hz (by simpa [show 4*s-1+1=4*s by omega] using hz')
  rw [show 4*s-1+2=4*s+1 by omega] at hd
  have hold := old_sums (c.take (4*s-1)) (c.drop (4*s+1)) hb.2.1 hb.2.2.1
  have hr := hold.symm.trans (show
      (edgeSums (c.take (4*s-1) ++ [0,0] ++ c.drop (4*s+1))).Perm (List.range (6*s-1)) by
    rw [← hd]; exact he)
  have hnew := surgery_sums (c.take (4*s-1)) (c.drop (4*s+1)) hb.1 hb.2.1 hb.2.2.1 hpos.1 hpos.2
  have hn := hnew.trans (enlarged_sum_interval (6*s-1) (by omega) _ hr)
  simpa only [surgery,extend,show 6*s-1+12=6*(s+2)-1 by omega] using hn

theorem surgery_patch_index (u v : List Nat) (i : Nat) (hi : i < 8) :
    (surgery u v)[6+u.length+i]? = ([6,4,0,0,1,1,2,5] : List Nat)[i]? := by
  simp only [surgery,List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map]
  have he : 6+u.length+i-6-u.length=i := by omega
  rw [he,List.getElem?_append_left (by simpa using hi)]

theorem extend_endpoints_anchors (s : Nat) (c : List Nat) (hc : CoreInvariant s c) :
    (extend s c)[0]?=some 3 ∧
    (extend s c)[6*(s+2)-1]?=some (3*(s+2)-4) ∧
    (extend s c)[4*(s+2)-2]?=some 4 ∧
    (extend s c)[4*(s+2)-1]?=some 0 ∧
    (extend s c)[4*(s+2)]?=some 0 ∧
    (extend s c)[4*(s+2)+1]?=some 1 := by
  have hs := hc.1
  have hlen := hc.2.1
  have hu : (c.take (4*s-1)).length=4*s-1 := by simp only [List.length_take,hlen]; omega
  have hb := core_part_boundaries s c hc
  have hlast : (extend s c).getLast?=some (3*(s+2)-4) := by
    simp only [extend,List.getLast?_append,List.getLast?_map,hb.2.2.2,Option.map_some]
    simp [next_last_value s hs]
  have helen := extend_length s c hs hlen
  rw [List.getLast?_eq_getElem?,helen] at hlast
  have hp (i : Nat) (hi : i < 8) := surgery_patch_index (c.take (4*s-1)) (c.drop (4*s+1)) i hi
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  simp only [hu] at h1 h2 h3 h4
  refine ⟨rfl,hlast,?_,?_,?_,?_⟩
  · simpa [surgery,extend,show 6+(4*s-1)+1=4*(s+2)-2 by omega] using h1
  · simpa [surgery,extend,show 6+(4*s-1)+2=4*(s+2)-1 by omega] using h2
  · simpa [surgery,extend,show 6+(4*s-1)+3=4*(s+2) by omega] using h3
  · simpa [surgery,extend,show 6+(4*s-1)+4=4*(s+2)+1 by omega] using h4

/-- The arbitrary raw-list recurrence, including every structural invariant. -/
theorem recurrence_preserves_invariant : RecurrencePreservesInvariant := by
  intro s c hc
  have hside := extend_side_partitions s c hc
  have hend := extend_endpoints_anchors s c hc
  exact ⟨by have hs := hc.1; omega, extend_length s c hc.1 hc.2.1,
    hside.1,hside.2,extend_edge_partition s c hc,hend⟩

/-- Unconditional existence of anchored balanced cores for every s>=2. -/
theorem uniform_anchored_cores : ∀ s, 2 ≤ s → ∃ c, CoreInvariant s c :=
  uniform_cores_if_recurrence recurrence_preserves_invariant
end GracefulBoundary







