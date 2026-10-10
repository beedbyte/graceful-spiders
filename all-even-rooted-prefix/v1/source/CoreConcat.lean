import FiniteAlphaTransfer

namespace GracefulBoundary.FixedDepth

def appendCore (p : Nat) (c d : List Nat) : List Nat :=
  c ++ d.map (fun x => p+x)

theorem side_interval (p q : Nat) :
    (List.range p ++ (List.range q).map (fun x => p+x)).Perm (List.range (p+q)) := by
  rw [← List.range'_eq_map_range]
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_range,count_band]
  repeat (any_goals split)
  all_goals omega

theorem sum_interval (p q : Nat) (hp : 4≤p) (hq : 4≤q) :
    (List.range (2*p-1) ++ (2*p-1)::List.range' (2*p) (2*q-1)).Perm
      (List.range (2*(p+q)-1)) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_cons,List.count_range,count_band,Nat.beq_eq_true_eq]
  repeat (any_goals split)
  all_goals omega

theorem edgeSums_add (p : Nat) (c : List Nat) :
    edgeSums (c.map (fun x => p+x)) = (edgeSums c).map (fun x => 2*p+x) := by
  induction c using edgeSums.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b xs ih =>
    simp only [List.map_cons,edgeSums]
    congr 1
    omega

theorem edgeSums_append_known (c d : List Nat) (a b : Nat)
    (hc : c.getLast?=some a) (hd : d.head?=some b) :
    edgeSums (c++d)=edgeSums c ++ (a+b)::edgeSums d := by
  cases d with
  | nil => simp at hd
  | cons y ys =>
    have hy : y=b := by simpa using hd
    subst y
    exact edgeSums_join c a b ys hc

theorem append_boundary_core (p q : Nat) (c d : List Nat)
    (hc : BoundaryCore p c) (hd : BoundaryCore q d) :
    BoundaryCore (p+q) (appendCore p c d) := by
  rcases hc with ⟨hp,hclen,hch,hcl,hcs,hcf,hct⟩
  rcases hd with ⟨hq,hdlen,hdh,hdl,hds,hdf,hdt⟩
  have even : (2*p)%2=0 := by omega
  have hlast : c.getLast?=some (p-4) := by
    rw [List.getLast?_eq_getElem?,hclen]
    exact hct
  have hhead : (d.map (fun x => p+x)).head?=some (p+3) := by
    rw [List.head?_map,List.head?_eq_getElem?,hdf]
    rfl
  refine ⟨by omega,?_,?_,?_,?_,?_,?_⟩
  · simp only [appendCore,List.length_append,List.length_map,hclen,hdlen]
    omega
  · simp only [appendCore,highs_append,hclen,even,ite_true,highs_map]
    exact (hch.append (hdh.map (fun x => p+x))).trans (side_interval p q)
  · simp only [appendCore,lows_append,hclen,even,ite_true,lows_map]
    exact (hcl.append (hdl.map (fun x => p+x))).trans (side_interval p q)
  · rw [appendCore,edgeSums_append_known c _ (p-4) (p+3) hlast hhead,
      edgeSums_add]
    have bridge : p-4+(p+3)=2*p-1 := by omega
    rw [bridge]
    have shifted := hds.map (fun x => 2*p+x)
    rw [← List.range'_eq_map_range] at shifted
    exact (hcs.append (shifted.cons (2*p-1))).trans (sum_interval p q hp hq)
  · rw [appendCore,List.getElem?_append_left (by omega)]
    exact hcf
  · rw [appendCore,List.getElem?_append_right (by omega)]
    rw [hclen,show 2*(p+q)-1-2*p=2*q-1 by omega]
    simp only [List.getElem?_map,hdt,Option.map_some]
    congr 1
    omega

structure CorePair (p z q : Nat) (c : List Nat) : Prop where
  boundary : BoundaryCore p c
  zeroPositive : 1≤z
  zeroInside : z≤2*p
  zeroEven : z%2=0
  maxPositive : 1≤q
  maxInside : q≤2*p
  maxOdd : q%2=1
  zeroL : c[z-1]?=some 0
  zeroH : c[q-1]?=some 0

theorem append_pair (p t z q : Nat) (c d : List Nat)
    (hc : CorePair p z q c) (hd : BoundaryCore t d) :
    CorePair (p+t) z q (appendCore p c d) := by
  refine ⟨append_boundary_core p t c d hc.boundary hd,
    hc.zeroPositive,by have := hc.zeroInside; omega,hc.zeroEven,
    hc.maxPositive,by have := hc.maxInside; omega,hc.maxOdd,?_,?_⟩
  · rw [appendCore,List.getElem?_append_left
      (by have := hc.zeroPositive; have := hc.zeroInside; rw [hc.boundary.2.1]; omega)]
    exact hc.zeroL
  · rw [appendCore,List.getElem?_append_left
      (by have := hc.maxPositive; have := hc.maxInside; rw [hc.boundary.2.1]; omega)]
    exact hc.zeroH

theorem core_pair_to_certificate (p z q : Nat) (c : List Nat)
    (hc : CorePair p z q c) :
    FiniteAlpha.Certificate p z q (completePath p c) := by
  have hz := complete_path_core_lookup p c (z-1) hc.boundary.2.1
    (by have := hc.zeroPositive; have := hc.zeroInside; omega)
  have hq := complete_path_core_lookup p c (q-1) hc.boundary.2.1
    (by have := hc.maxPositive; have := hc.maxInside; omega)
  rw [coreLabels_lookup,hc.zeroL] at hz
  rw [coreLabels_lookup,hc.zeroH] at hq
  have ho : ¬ (z-1)%2=0 := by have := hc.zeroEven; have := hc.zeroPositive; omega
  have he : (q-1)%2=0 := by have := hc.maxOdd; have := hc.maxPositive; omega
  simp only [ho,ite_false,Option.map_some] at hz
  simp only [he,ite_true,Option.map_some,Nat.sub_zero] at hq
  refine ⟨hc.zeroPositive,by have := hc.zeroInside; omega,hc.maxPositive,
    by have := hc.maxInside; omega,boundary_shell_bridge p c hc.boundary,?_,?_⟩
  · simpa only [show 2*p+2-(z-1)=2*p+3-z by
      have := hc.zeroPositive; have := hc.zeroInside; omega] using hz
  · simpa only [show 2*p+2-(q-1)=2*p+3-q by
      have := hc.maxPositive; have := hc.maxInside; omega] using hq

theorem core_pair_spider_transfer (p z q n m : Nat) (c : List Nat)
    (hc : CorePair p z q c) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m (2*p+3) → Nat,
      Graceful (spiderGraph n m (2*p+3)) (n*(2*p+3)+m) f ∧
      f (.arm a ⟨z-1,by have := hc.zeroInside; omega⟩)=0) ∧
    (∃ f : SpiderVertex n m (2*p+3) → Nat,
      Graceful (spiderGraph n m (2*p+3)) (n*(2*p+3)+m) f ∧
      f (.arm a ⟨q-1,by have := hc.maxInside; omega⟩)=0) := by
  exact FiniteAlpha.prescribed_zero p z q n m (completePath p c)
    (core_pair_to_certificate p z q c hc) hn a

end GracefulBoundary.FixedDepth
