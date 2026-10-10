import VariableGadget
namespace GracefulBoundary.Variable

structure AnchoredCore (p d : Nat) (c : List Nat) : Prop where
  size : 6 ≤ p
  depth : 2 ≤ d
  even : d%2=0
  inside : d+1 < 2*p
  length : c.length=2*p
  high : (highs c).Perm (List.range p)
  low : (lows c).Perm (List.range p)
  sums : (edgeSums c).Perm (List.range (2*p-1))
  first : c[0]?=some 3
  last : c[2*p-1]?=some (p-4)
  patch4 : c[d-2]?=some 4
  zeroL : c[d-1]?=some 0
  zeroH : c[d]?=some 0
  patch1 : c[d+1]?=some 1

def extend (g : Gadget) (d : Nat) (c : List Nat) := surgery g (c.take (d-1)) (c.drop (d+1))

theorem bump_range (p : Nat) (hp : 1 ≤ p) :
    (List.range p).map bump9 = 0 :: List.range' 10 (p-1) := by
  obtain ⟨n,hn⟩ : ∃ n, p=n+1 := ⟨p-1,by omega⟩
  subst p
  rw [List.range_succ_eq_map]
  simp only [List.map_cons,List.map_map]
  have hf : (fun x => bump9 (x+1)) = (fun x => 10+x) := by
    funext x
    rw [bump9_positive _ (by omega)]
    omega
  change bump9 0 :: (List.range n).map (fun x => bump9 (x+1)) = _
  rw [hf]
  simp [bump9,List.range'_eq_map_range]

theorem side_interval_extension (p : Nat) (hp : 1 ≤ p) :
    ((List.range p).map bump9 ++ List.range' 1 9).Perm (List.range (p+9)) := by
  rw [bump_range p hp]
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_cons,count_band,List.count_range,Nat.beq_eq_true_eq]
  repeat (any_goals split)
  all_goals omega

theorem decomposition (p d : Nat) (c : List Nat) (h : AnchoredCore p d c) :
    c=c.take (d-1) ++ [0,0] ++ c.drop (d+1) := by
  have hd := h.depth
  simpa only [show d-1+2=d+1 by omega] using
    split_two c (d-1) 0 0 h.zeroL (by simpa only [show d-1+1=d by omega] using h.zeroH)

theorem part_length (p d : Nat) (c : List Nat) (h : AnchoredCore p d c) :
    (c.take (d-1)).length=d-1 := by
  have hd := h.inside
  simp only [List.length_take,h.length]
  omega

theorem parts_positive (p d : Nat) (c : List Nat) (h : AnchoredCore p d c) :
    (∀ x ∈ c.take (d-1),0<x) ∧ (∀ x ∈ c.drop (d+1),0<x) := by
  have hh := h.high.count_eq 0
  have hl := h.low.count_eq 0
  have hp : 0<p := by have hs := h.size; omega
  simp only [List.count_range,hp,ite_true] at hh hl
  have hc := count_sides 0 c
  have hd := decomposition p d c h
  have hz : c.count 0=2 := by omega
  rw [hd] at hz
  simp only [List.count_append] at hz
  simp at hz
  have hu : (c.take (d-1)).count 0=0 := by omega
  have hv : (c.drop (d+1)).count 0=0 := by omega
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

theorem part_boundaries (p d : Nat) (c : List Nat) (h : AnchoredCore p d c) :
    (c.take (d-1)).head?=some 3 ∧ (c.take (d-1)).getLast?=some 4 ∧
    (c.drop (d+1)).head?=some 1 ∧ (c.drop (d+1)).getLast?=some (p-4) := by
  have hd := h.depth
  have hi := h.inside
  have hnz : d-1≠0 := by omega
  have hshort : ¬ c.length ≤ d+1 := by rw [h.length]; omega
  refine ⟨?_,?_,?_,?_⟩
  · rw [List.head?_eq_getElem?,List.getElem?_take_of_lt (by omega)]
    exact h.first
  · simp [List.getLast?_take,hnz,show d-1-1=d-2 by omega,h.patch4]
  · simpa using h.patch1
  · rw [List.getLast?_drop]
    simp only [hshort,ite_false]
    rw [List.getLast?_eq_getElem?,h.length]
    exact h.last

theorem extend_sides (g : Gadget) (p d : Nat) (c : List Nat) (h : AnchoredCore p d c) :
    (highs (extend g d c)).Perm (List.range (p+9)) ∧
    (lows (extend g d c)).Perm (List.range (p+9)) := by
  have he := h.even
  have hd := h.depth
  have hu : (c.take (d-1)).length%2=1 := by rw [part_length p d c h]; omega
  have hh := surgery_highs g (c.take (d-1)) (c.drop (d+1)) hu
  have hl := surgery_lows g (c.take (d-1)) (c.drop (d+1)) hu
  rw [← decomposition p d c h] at hh hl
  have hp := side_interval_extension p (by have hs := h.size; omega)
  exact ⟨hh.trans (((h.high.map bump9).append_right _).trans hp),
    hl.trans (((h.low.map bump9).append_right _).trans hp)⟩

theorem shifted_rest_interval (N : Nat) (hN : 5 ≤ N) (r : List Nat)
    (hr : ([0,1,4]++r).Perm (List.range N)) :
    (r.map (fun x => x+18)).Perm ([20,21]++List.range' 23 (N-5)) := by
  have h := List.Perm.map (fun x => x+18) (remove_three_sum_values N hN r hr)
  have hf : (fun x : Nat => x+18) = (fun x => 18+x) := by funext x; omega
  have hrange : (List.range' 5 (N-5)).map (fun x => x+18)=List.range' 23 (N-5) := by
    rw [hf,List.map_add_range']
  simpa only [List.map_append,List.map_cons,List.map_nil,hrange] using h

set_option maxHeartbeats 1000000 in
theorem enlarged_sum_interval (g : Gadget) (N : Nat) (hN : 5 ≤ N) (r : List Nat)
    (hr : ([0,1,4]++r).Perm (List.range N)) :
    (r.map (fun x => x+18) ++ [0] ++ inserted g).Perm (List.range (N+18)) := by
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
    (edgeSums (extend g d c)).Perm (List.range (2*(p+9)-1)) := by
  have hs := h.size
  have hb := part_boundaries p d c h
  have hpos := parts_positive p d c h
  have hold := old_sums (c.take (d-1)) (c.drop (d+1)) hb.2.1 hb.2.2.1
  have hr := hold.symm.trans (show
    (edgeSums (c.take (d-1)++[0,0]++c.drop (d+1))).Perm (List.range (2*p-1)) by
      rw [← decomposition p d c h]; exact h.sums)
  have hnew := surgery_sums g (c.take (d-1)) (c.drop (d+1)) hb.1 hb.2.1 hb.2.2.1 hpos.1 hpos.2
  have hn := hnew.trans (enlarged_sum_interval g (2*p-1) (by omega) _ hr)
  simpa only [extend,show 2*p-1+18=2*(p+9)-1 by omega] using hn


theorem extend_length (g : Gadget) (p d : Nat) (c : List Nat) (h : AnchoredCore p d c) :
    (extend g d c).length=2*(p+9) := by
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
  rw [show before g ++ ([0,0] ++ (after g ++ v.map bump9)) =
    (before g ++ [0,0] ++ after g) ++ v.map bump9 by simp only [List.append_assoc]]
  simpa only [List.append_assoc] using List.getElem?_append_left hi (l₂ := v.map bump9)

theorem gadget_patch (g : Gadget) :
    1 ≤ (before g).length ∧
    (before g).length+2 < (before g++[0,0]++after g).length ∧
    (before g++[0,0]++after g)[(before g).length-1]?=some 4 ∧
    (before g++[0,0]++after g)[(before g).length]?=some 0 ∧
    (before g++[0,0]++after g)[(before g).length+1]?=some 0 ∧
    (before g++[0,0]++after g)[(before g).length+2]?=some 1 := by
  cases g <;> decide

theorem extend_endpoints (g : Gadget) (p d : Nat) (c : List Nat) (h : AnchoredCore p d c) :
    (extend g d c)[0]?=some 3 ∧ (extend g d c)[2*(p+9)-1]?=some (p+9-4) := by
  have hb := (part_boundaries p d c h).2.2.2
  have hp := h.size
  have hlast : (extend g d c).getLast?=some (p+9-4) := by
    simp only [extend,surgery,List.getLast?_append,List.getLast?_map,hb,Option.map_some]
    rw [bump9_positive _ (by omega)]
    have he : p-4+9=p+9-4 := by omega
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

/-- All six raw-list q9 surgeries preserve every anchored-core invariant. -/
theorem q9_preserves_invariant (g : Gadget) (p d : Nat) (c : List Nat)
    (h : AnchoredCore p d c) : AnchoredCore (p+9) (d+delta g) (extend g d c) := by
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

end GracefulBoundary.Variable
