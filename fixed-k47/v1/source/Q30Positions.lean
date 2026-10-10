import Q30Graft
namespace GracefulBoundary.Q30

theorem extend_length (k z : Nat) (c : List Nat) (h : State k z c) :
    (extend z c).length=2*(k+30)+1 := by
  have lens := part_lengths k z c h
  simp only [extend,surgery,List.length_append,List.length_map,lens.1,lens.2,B,D,A,
    List.length_cons,List.length_nil]
  have hi := h.zeroInside
  omega

theorem surgery_patch_index (u v : List Nat) (i : Nat) (hi : i<32) :
    (surgery u v)[u.length+i]?=(B++[0,0]++D)[i]? := by
  simp only [surgery,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map,show u.length+i-u.length=i by omega]
  rw [show B++([0,0]++(D++(v.map (fun x=>x+30)++A)))=
    (B++[0,0]++D)++(v.map (fun x=>x+30)++A) by simp only [List.append_assoc]]
  exact List.getElem?_append_left (by simpa only [B,D,List.length_append,List.length_cons,List.length_nil] using hi)

theorem extend_patch (k z : Nat) (c : List Nat) (h : State k z c) :
    (extend z c)[z+1]?=some 1 ∧ (extend z c)[z+2]?=some 0 ∧
    (extend z c)[z+3]?=some 0 ∧ (extend z c)[z+4]?=some 2 := by
  have lens := part_lengths k z c h
  have look (i : Nat) (hi : i<32) := surgery_patch_index (c.take z) (c.drop (z+2)) i hi
  have h1 := look 1 (by decide)
  have h0 := look 2 (by decide)
  have h00 := look 3 (by decide)
  have h2 := look 4 (by decide)
  simp only [lens.1] at h1 h0 h00 h2
  exact ⟨h1.trans (by rfl),h0.trans (by rfl),h00.trans (by rfl),h2.trans (by rfl)⟩

theorem surgery_right_index (u v : List Nat) (i : Nat) (hi : i<v.length) :
    (surgery u v)[u.length+32+i]?=v[i]?.map (fun x=>x+30) := by
  unfold surgery
  rw [show u.map (fun x=>x+30)++B++[0,0]++D++v.map (fun x=>x+30)++A=
    (u.map (fun x=>x+30)++B++[0,0]++D)++(v.map (fun x=>x+30)++A) by simp only [List.append_assoc]]
  have prefixLen : (u.map (fun x=>x+30)++B++[0,0]++D).length=u.length+32 := by
    simp only [List.length_map,List.length_append,B,D,List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by rw [prefixLen]; omega),prefixLen]
  rw [show u.length+32+i-(u.length+32)=i by omega]
  rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]

theorem extend_midpoint (k z : Nat) (c : List Nat) (h : State k z c) :
    (extend z c)[k+30]?=some (k+29) := by
  have hi := h.zeroInside
  have hs := h.size
  have lens := part_lengths k z c h
  have bound : k-(z+2)<(c.drop (z+2)).length := by rw [lens.2]; omega
  have look := surgery_right_index (c.take z) (c.drop (z+2)) (k-(z+2)) bound
  have old : (c.drop (z+2))[k-(z+2)]?=some (k-1) := by
    rw [List.getElem?_drop,show z+2+(k-(z+2))=k by omega]
    exact h.midpoint
  rw [lens.1,show z+32+(k-(z+2))=k+30 by omega,old] at look
  simpa only [extend,Option.map_some,show k-1+30=k+29 by omega] using look

theorem extend_terminal (k z : Nat) (c : List Nat) (h : State k z c) :
    (extend z c)[2*(k+30)]?=some 16 := by
  have last : (extend z c).getLast?=some 16 := by
    simp only [extend,surgery,List.getLast?_append,show A.getLast?=some 16 by rfl]
    rfl
  rw [List.getLast?_eq_getElem?,extend_length k z c h,show 2*(k+30)+1-1=2*(k+30) by omega] at last
  exact last

/-- Unbounded preservation of every whole-path premise, including actual midpoint. -/
theorem q30_preserves_state (k z : Nat) (c : List Nat) (h : State k z c) :
    State (k+30) (z+2) (extend z c) := by
  have hi := h.zeroInside
  have hs := h.size
  have ho := h.odd
  have hz := h.zeroOdd
  have sides := extend_sides k z c h
  have patch := extend_patch k z c h
  refine ⟨by omega,by omega,⟨by omega,by omega⟩,by omega,extend_length k z c h,
    ?_,sides.2,extend_sums k z c h,?_,?_,patch.2.1,?_,?_,extend_terminal k z c h⟩
  · simpa only [show k+30+1=k+31 by omega] using sides.1
  · simpa only [show k+30-1=k+29 by omega] using extend_midpoint k z c h
  · simpa only [show z+2-1=z+1 by omega] using patch.1
  · simpa only [show z+2+1=z+3 by omega] using patch.2.2.1
  · simpa only [show z+2+2=z+4 by omega] using patch.2.2.2

end GracefulBoundary.Q30
