import Q18Gadget
namespace GracefulBoundary.Variable.Q18

def extend (g : Gadget) (d : Nat) (c : List Nat) := surgery g (c.take (d-1)) (c.drop (d+1))

theorem bump_range (p : Nat) (hp : 1 ≤ p) :
    (List.range p).map bump18 = 0 :: List.range' 19 (p-1) := by
  obtain ⟨n,hn⟩ : ∃ n, p=n+1 := ⟨p-1,by omega⟩
  subst p
  rw [List.range_succ_eq_map]
  simp only [List.map_cons,List.map_map]
  have hf : (fun x => bump18 (x+1)) = (fun x => 19+x) := by
    funext x
    rw [bump18_positive _ (by omega)]
    omega
  change bump18 0 :: (List.range n).map (fun x => bump18 (x+1)) = _
  rw [hf]
  simp [bump18,List.range'_eq_map_range]

theorem side_interval_extension (p : Nat) (hp : 1 ≤ p) :
    ((List.range p).map bump18 ++ List.range' 1 18).Perm (List.range (p+18)) := by
  rw [bump_range p hp]
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_cons,count_band,List.count_range,Nat.beq_eq_true_eq]
  repeat (any_goals split)
  all_goals omega

theorem extend_sides (g : Gadget) (p d : Nat) (c : List Nat) (h : AnchoredCore p d c) :
    (highs (extend g d c)).Perm (List.range (p+18)) ∧
    (lows (extend g d c)).Perm (List.range (p+18)) := by
  have he := h.even
  have hd := h.depth
  have hu : (c.take (d-1)).length%2=1 := by rw [part_length p d c h]; omega
  have hh := surgery_highs g (c.take (d-1)) (c.drop (d+1)) hu
  have hl := surgery_lows g (c.take (d-1)) (c.drop (d+1)) hu
  rw [← decomposition p d c h] at hh hl
  have hp := side_interval_extension p (by have hs := h.size; omega)
  exact ⟨hh.trans (((h.high.map bump18).append_right _).trans hp),
    hl.trans (((h.low.map bump18).append_right _).trans hp)⟩

theorem shifted_rest_interval (N : Nat) (hN : 5 ≤ N) (r : List Nat)
    (hr : ([0,1,4]++r).Perm (List.range N)) :
    (r.map (fun x => x+36)).Perm ([38,39]++List.range' 41 (N-5)) := by
  have h := List.Perm.map (fun x => x+36) (remove_three_sum_values N hN r hr)
  have hf : (fun x : Nat => x+36) = (fun x => 36+x) := by funext x; omega
  have hrange : (List.range' 5 (N-5)).map (fun x => x+36)=List.range' 41 (N-5) := by
    rw [hf,List.map_add_range']
  simpa only [List.map_append,List.map_cons,List.map_nil,hrange] using h

set_option maxHeartbeats 1000000 in
theorem enlarged_sum_interval (g : Gadget) (N : Nat) (hN : 5 ≤ N) (r : List Nat)
    (hr : ([0,1,4]++r).Perm (List.range N)) :
    (r.map (fun x => x+36) ++ [0] ++ inserted g).Perm (List.range (N+36)) := by
  have hm := shifted_rest_interval N hN r hr
  apply List.perm_iff_count.mpr
  intro x
  have hc := hm.count_eq x
  have hi := (gadget_inserted g).count_eq x
  simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,count_band,Nat.beq_eq_true_eq] at hc hi ⊢
  rw [hc,hi]
  repeat (any_goals split)
  all_goals omega

theorem extend_sums (g : Gadget) (p d : Nat) (c : List Nat) (h : AnchoredCore p d c) :
    (edgeSums (extend g d c)).Perm (List.range (2*(p+18)-1)) := by
  have hs := h.size
  have hb := part_boundaries p d c h
  have hpos := parts_positive p d c h
  have hold := old_sums (c.take (d-1)) (c.drop (d+1)) hb.2.1 hb.2.2.1
  have hr := hold.symm.trans (show
    (edgeSums (c.take (d-1)++[0,0]++c.drop (d+1))).Perm (List.range (2*p-1)) by
      rw [← decomposition p d c h]; exact h.sums)
  have hnew := surgery_sums g (c.take (d-1)) (c.drop (d+1)) hb.1 hb.2.1 hb.2.2.1 hpos.1 hpos.2
  have hn := hnew.trans (enlarged_sum_interval g (2*p-1) (by omega) _ hr)
  simpa only [extend,show 2*p-1+36=2*(p+18)-1 by omega] using hn


theorem extend_length (g : Gadget) (p d : Nat) (c : List Nat) (h : AnchoredCore p d c) :
    (extend g d c).length=2*(p+18) := by
  have hd := h.depth
  have hi := h.inside
  have hg := (gadget_lengths g).2.2.2.1
  simp only [extend,surgery,List.length_append,List.length_map,List.length_cons,List.length_nil,
    List.length_take,List.length_drop,h.length]
  omega

theorem surgery_patch_index (g : Gadget) (u v : List Nat) (i : Nat)
    (hi : i < (before g ++ [0,0] ++ after g).length) :
    (surgery g u v)[(pre g).length+u.length+i]? = (before g ++ [0,0] ++ after g)[i]? := by
  simp only [surgery,List.append_assoc]
  rw [List.getElem?_append_right (by first | omega | (simp only [List.length_map]; omega))]
  rw [List.getElem?_append_right (by first | omega | (simp only [List.length_map]; omega))]
  simp only [List.length_map]
  have he : (pre g).length+u.length+i-(pre g).length-u.length=i := by omega
  rw [he]
  rw [show before g ++ ([0,0] ++ (after g ++ v.map bump18)) =
    (before g ++ [0,0] ++ after g) ++ v.map bump18 by simp only [List.append_assoc]]
  simpa only [List.append_assoc] using List.getElem?_append_left hi (l₂ := v.map bump18)

theorem gadget_patch (g : Gadget) :
    1 ≤ (before g).length ∧
    (before g).length+2 < (before g++[0,0]++after g).length ∧
    (before g++[0,0]++after g)[(before g).length-1]?=some 4 ∧
    (before g++[0,0]++after g)[(before g).length]?=some 0 ∧
    (before g++[0,0]++after g)[(before g).length+1]?=some 0 ∧
    (before g++[0,0]++after g)[(before g).length+2]?=some 1 := by
  cases g <;> decide

theorem extend_endpoints (g : Gadget) (p d : Nat) (c : List Nat) (h : AnchoredCore p d c) :
    (extend g d c)[0]?=some 3 ∧ (extend g d c)[2*(p+18)-1]?=some (p+18-4) := by
  have hb := (part_boundaries p d c h).2.2.2
  have hp := h.size
  have hlast : (extend g d c).getLast?=some (p+18-4) := by
    simp only [extend,surgery,List.getLast?_append,List.getLast?_map,hb,Option.map_some]
    rw [bump18_positive _ (by omega)]
    have he : p-4+18=p+18-4 := by omega
    simp [he]
  rw [List.getLast?_eq_getElem?,extend_length g p d c h] at hlast
  refine ⟨?_,hlast⟩
  cases g <;> rfl

theorem extend_patch (g : Gadget) (p d : Nat) (c : List Nat) (h : AnchoredCore p d c) :
    (extend g d c)[d+delta g-2]?=some 4 ∧
    (extend g d c)[d+delta g-1]?=some 0 ∧
    (extend g d c)[d+delta g]?=some 0 ∧
    (extend g d c)[d+delta g+1]?=some 1 := by
  have hd := h.depth
  obtain ⟨hb,hbnd,h4,h0,h00,h1⟩ := gadget_patch g
  have hp (i : Nat) (hi : i < (before g++[0,0]++after g).length) :=
    surgery_patch_index g (c.take (d-1)) (c.drop (d+1)) i hi
  have e4 := (hp ((before g).length-1) (by omega)).trans h4
  have e0 := (hp ((before g).length) (by omega)).trans h0
  have e00 := (hp ((before g).length+1) (by omega)).trans h00
  have e1 := (hp ((before g).length+2) (by omega)).trans h1
  simp only [part_length p d c h] at e4 e0 e00 e1
  have a4 : (pre g).length+(d-1)+((before g).length-1)=d+delta g-2 := by unfold delta; omega
  have a0 : (pre g).length+(d-1)+(before g).length=d+delta g-1 := by unfold delta; omega
  have a00 : (pre g).length+(d-1)+((before g).length+1)=d+delta g := by unfold delta; omega
  have a1 : (pre g).length+(d-1)+((before g).length+2)=d+delta g+1 := by unfold delta; omega
  exact ⟨by simpa only [extend,a4] using e4,by simpa only [extend,a0] using e0,
    by simpa only [extend,a00] using e00,by simpa only [extend,a1] using e1⟩

/-- The raw-list q18 surgeries preserve every anchored-core invariant. -/
theorem q18_preserves_invariant (g : Gadget) (p d : Nat) (c : List Nat)
    (h : AnchoredCore p d c) : AnchoredCore (p+18) (d+delta g) (extend g d c) := by
  have hp := h.size
  have hd := h.depth
  have hi := h.inside
  have he := h.even
  have hg := (gadget_lengths g).2.2.2.2
  have hsides := extend_sides g p d c h
  have ends := extend_endpoints g p d c h
  have patch := extend_patch g p d c h
  exact ⟨by omega,by omega,by omega,by omega,extend_length g p d c h,
    hsides.1,hsides.2,extend_sums g p d c h,ends.1,ends.2,
    patch.1,patch.2.1,patch.2.2.1,patch.2.2.2⟩

end GracefulBoundary.Variable.Q18
