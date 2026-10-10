import SpiderTheorem
namespace GracefulBoundary.SecondPair

/-- Strengthened recurrence contract applies only from s=4 upward. -/
def CoreInvariant (s : Nat) (c : List Nat) : Prop :=
  4 ≤ s ∧ c.length=6*s ∧
  (highs c).Perm (List.range (3*s)) ∧ (lows c).Perm (List.range (3*s)) ∧
  (edgeSums c).Perm (List.range (6*s-1)) ∧ c[0]?=some 3 ∧ c[6*s-1]?=some (3*s-4) ∧
  c[4*s]?=some 4 ∧ c[4*s+1]?=some 0 ∧ c[4*s+2]?=some 0 ∧ c[4*s+3]?=some 1

def AnchoredCore (s : Nat) (c : List Nat) : Prop :=
  BoundaryCore (3*s) c ∧ c[4*s+1]?=some 0 ∧ c[4*s+2]?=some 0

def extend (s : Nat) (c : List Nat) : List Nat :=
  [3,5,6,3,2,4] ++ (c.take (4*s+1)).map bump ++
    [6,4,0,0,1,1,2,5] ++ (c.drop (4*s+3)).map bump

def RecurrencePreservesInvariant : Prop :=
  ∀ s c, CoreInvariant s c → CoreInvariant (s+2) (extend s c)

def seed2 : List Nat := [3,4,4,5,5,1,2,3,1,0,0,2]
def seed3 : List Nat := [3,4,6,8,8,7,5,6,7,1,2,3,1,0,0,2,4,5]
def seed4 : List Nat := [3,3,2,5,10,11,11,9,9,10,7,7,6,6,5,4,4,0,0,1,1,2,8,8]
def seed5 : List Nat := [3,3,2,6,9,14,14,13,13,12,12,10,11,9,10,8,8,5,7,7,4,0,0,1,1,2,5,4,6,11]

theorem seed2_valid : AnchoredCore 2 seed2 := by
  unfold AnchoredCore BoundaryCore
  decide
theorem seed3_valid : AnchoredCore 3 seed3 := by
  unfold AnchoredCore BoundaryCore
  decide
theorem seed4_valid : CoreInvariant 4 seed4 := by unfold CoreInvariant; decide
theorem seed5_valid : CoreInvariant 5 seed5 := by unfold CoreInvariant; decide

theorem extend_length (s : Nat) (c : List Nat) (hs : 4 ≤ s) (hc : c.length=6*s) :
    (extend s c).length=6*(s+2) := by
  simp only [extend,List.length_append,List.length_cons,List.length_nil,
    List.length_map,List.length_take,List.length_drop,hc]
  omega
theorem core_zero_count (s : Nat) (c : List Nat) (hc : CoreInvariant s c) : c.count 0=2 := by
  rcases hc with ⟨hs,_,hh,hl,_⟩
  have hhigh := hh.count_eq 0
  have hlow := hl.count_eq 0
  have hp : 0 < 3*s := by omega
  simp only [List.count_range, hp, ite_true] at hhigh hlow
  have ht := count_sides 0 c
  omega

theorem core_parts_positive (s : Nat) (c : List Nat) (hc : CoreInvariant s c) :
    (∀ x ∈ c.take (4*s+1), 0 < x) ∧ (∀ x ∈ c.drop (4*s+3), 0 < x) := by
  have hs := hc.1
  have hcount := core_zero_count s c hc
  obtain ⟨_,_,_,_,_,_,_,_,hz,hz',_⟩ := hc
  have hzindex : 4*s+1+1=4*s+2 := by omega
  have hzindex' : 4*s+1+2=4*s+3 := by omega
  have hd := split_two c (4*s+1) 0 0 hz (by simpa [hzindex] using hz')
  rw [hzindex'] at hd
  rw [hd] at hcount
  simp only [List.count_append] at hcount
  simp at hcount
  have hu : (c.take (4*s+1)).count 0=0 := by omega
  have hv : (c.drop (4*s+3)).count 0=0 := by omega
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

theorem extend_side_partitions (s : Nat) (c : List Nat) (hc : CoreInvariant s c) :
    (highs (extend s c)).Perm (List.range (3*(s+2))) ∧
    (lows (extend s c)).Perm (List.range (3*(s+2))) := by
  have hs := hc.1
  rcases hc with ⟨_,hlen,hh,hl,_,_,_,_,hz,hz',_⟩
  have hd := split_two c (4*s+1) 0 0 hz (by simpa [show 4*s+1+1=4*s+2 by omega] using hz')
  rw [show 4*s+1+2=4*s+3 by omega] at hd
  have hu : (c.take (4*s+1)).length%2=1 := by
    simp only [List.length_take,hlen]; omega
  have eh := surgery_highs (c.take (4*s+1)) (c.drop (4*s+3)) hu
  have el := surgery_lows (c.take (4*s+1)) (c.drop (4*s+3)) hu
  rw [← hd] at eh el
  have hmhigh := (List.Perm.map bump hh).append high_gadget
  have hmlow := (List.Perm.map bump hl).append low_gadget
  have hp := side_interval_extension (3*s) (by omega)
  have ht : 3*s+6=3*(s+2) := by omega
  constructor
  · simpa only [surgery,extend,ht] using eh.trans (hmhigh.trans hp)
  · simpa only [surgery,extend,ht] using el.trans (hmlow.trans hp)

theorem core_part_boundaries (s : Nat) (c : List Nat) (hc : CoreInvariant s c) :
    (c.take (4*s+1)).head?=some 3 ∧
    (c.take (4*s+1)).getLast?=some 4 ∧
    (c.drop (4*s+3)).head?=some 1 ∧
    (c.drop (4*s+3)).getLast?=some (3*s-4) := by
  rcases hc with ⟨hs,hlen,_,_,_,hf,ht,hn,_,_,hv⟩
  have hi : 4*s+1-1=4*s := by omega
  have hshort : ¬ c.length ≤ 4*s+3 := by omega
  refine ⟨?_,?_,?_,?_⟩
  · rw [List.head?_eq_getElem?,List.getElem?_take_of_lt (by omega)]
    exact hf
  · simp [List.getLast?_take,hi,hn]
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
  have hd := split_two c (4*s+1) 0 0 hz (by simpa [show 4*s+1+1=4*s+2 by omega] using hz')
  rw [show 4*s+1+2=4*s+3 by omega] at hd
  have hold := old_sums (c.take (4*s+1)) (c.drop (4*s+3)) hb.2.1 hb.2.2.1
  have hr := hold.symm.trans (show
      (edgeSums (c.take (4*s+1) ++ [0,0] ++ c.drop (4*s+3))).Perm (List.range (6*s-1)) by
    rw [← hd]; exact he)
  have hnew := surgery_sums (c.take (4*s+1)) (c.drop (4*s+3)) hb.1 hb.2.1 hb.2.2.1 hpos.1 hpos.2
  have hn := hnew.trans (enlarged_sum_interval (6*s-1) (by omega) _ hr)
  simpa only [surgery,extend,show 6*s-1+12=6*(s+2)-1 by omega] using hn

theorem extend_endpoints_anchors (s : Nat) (c : List Nat) (hc : CoreInvariant s c) :
    (extend s c)[0]?=some 3 ∧
    (extend s c)[6*(s+2)-1]?=some (3*(s+2)-4) ∧
    (extend s c)[4*(s+2)]?=some 4 ∧
    (extend s c)[4*(s+2)+1]?=some 0 ∧
    (extend s c)[4*(s+2)+2]?=some 0 ∧
    (extend s c)[4*(s+2)+3]?=some 1 := by
  have hs := hc.1
  have hlen := hc.2.1
  have hu : (c.take (4*s+1)).length=4*s+1 := by simp only [List.length_take,hlen]; omega
  have hb := core_part_boundaries s c hc
  have hlast : (extend s c).getLast?=some (3*(s+2)-4) := by
    simp only [extend,List.getLast?_append,List.getLast?_map,hb.2.2.2,Option.map_some]
    simp [next_last_value s (by omega)]
  have helen := extend_length s c hs hlen
  rw [List.getLast?_eq_getElem?,helen] at hlast
  have hp (i : Nat) (hi : i < 8) := surgery_patch_index (c.take (4*s+1)) (c.drop (4*s+3)) i hi
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  simp only [hu] at h1 h2 h3 h4
  refine ⟨rfl,hlast,?_,?_,?_,?_⟩
  · simpa [surgery,extend,show 6+(4*s+1)+1=4*(s+2) by omega] using h1
  · simpa [surgery,extend,show 6+(4*s+1)+2=4*(s+2)+1 by omega] using h2
  · simpa [surgery,extend,show 6+(4*s+1)+3=4*(s+2)+2 by omega] using h3
  · simpa [surgery,extend,show 6+(4*s+1)+4=4*(s+2)+3 by omega] using h4

theorem recurrence_preserves_invariant : RecurrencePreservesInvariant := by
  intro s c hc
  have hside := extend_side_partitions s c hc
  have hend := extend_endpoints_anchors s c hc
  exact ⟨by have hs := hc.1; omega, extend_length s c hc.1 hc.2.1,
    hside.1,hside.2,extend_edge_partition s c hc,hend⟩




theorem strong_core_is_anchored (s : Nat) (c : List Nat) (hc : CoreInvariant s c) :
    AnchoredCore s c := by
  rcases hc with ⟨hs,hl,hh,ht,he,hfirst,hlast,_,hz,hm,_⟩
  refine ⟨⟨by omega,?_,hh,ht,?_,hfirst,?_⟩,hz,hm⟩
  · simpa [show 2*(3*s)=6*s by omega] using hl
  · simpa [show 2*(3*s)=6*s by omega] using he
  · simpa [show 2*(3*s)=6*s by omega] using hlast

theorem uniform_strong_cores : ∀ s, 4 ≤ s → ∃ c, CoreInvariant s c := by
  have hi := induction_from_two_seeds (fun t => ∃ c,CoreInvariant (t+2) c)
    ⟨seed4,seed4_valid⟩ ⟨seed5,seed5_valid⟩
    (by intro t _ ht; obtain ⟨c,hc⟩ := ht; exact ⟨extend (t+2) c,recurrence_preserves_invariant (t+2) c hc⟩)
  intro s hs
  simpa only [show s-2+2=s by omega] using hi (s-2) (by omega)

theorem uniform_anchored_cores : ∀ s, 2 ≤ s → ∃ c, AnchoredCore s c := by
  intro s hs
  by_cases h2 : s=2
  · subst s; exact ⟨seed2,seed2_valid⟩
  by_cases h3 : s=3
  · subst s; exact ⟨seed3,seed3_valid⟩
  obtain ⟨c,hc⟩ := uniform_strong_cores s (by omega)
  exact ⟨c,strong_core_is_anchored s c hc⟩

/-- The small exceptions genuinely lack the recurrence's local window. -/
theorem exceptional_neighbours :
    seed2[8]?=some 1 ∧ seed2[11]?=some 2 ∧ seed3[12]?=some 1 ∧ seed3[15]?=some 2 := by decide

theorem rejects_recurrence_from_seed2 : ¬ BoundaryCore 12 (extend 2 seed2) := by
  unfold BoundaryCore
  decide

theorem rejects_recurrence_from_seed3 : ¬ BoundaryCore 15 (extend 3 seed3) := by
  unfold BoundaryCore
  decide

end GracefulBoundary.SecondPair
