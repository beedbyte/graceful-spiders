import AllLengthsDepth

namespace GracefulBoundary.ReverseComplement
open FixedDepth

def reflect (p : Nat) (x : Nat) : Nat := p-1-x
def transform (p : Nat) (c : List Nat) : List Nat := c.reverse.map (reflect p)

theorem sides_reverse (c : List Nat) :
    highs c.reverse=(if c.length%2=0 then (lows c).reverse else (highs c).reverse) ∧
    lows c.reverse=(if c.length%2=0 then (highs c).reverse else (lows c).reverse) := by
  induction c with
  | nil => simp [highs,lows]
  | cons a c ih =>
    by_cases he : c.length%2=0
    · have ho : ¬ (c.length+1)%2=0 := by omega
      simp [List.reverse_cons,highs_append,lows_append,ih.1,ih.2,he,ho,highs,lows]
    · have ho : (c.length+1)%2=0 := by omega
      simp [List.reverse_cons,highs_append,lows_append,ih.1,ih.2,he,ho,highs,lows]

theorem edgeSums_reverse (c : List Nat) : edgeSums c.reverse=(edgeSums c).reverse := by
  induction c with
  | nil => rfl
  | cons a c ih =>
    cases c with
    | nil => rfl
    | cons b c =>
      rw [List.reverse_cons,edgeSums_join _ b a [] (by simp),ih]
      simp [edgeSums,Nat.add_comm]

theorem reflect_range (p : Nat) :
    ((List.range p).map (reflect p)).Perm (List.range p) := by
  have he : (List.range p).reverse=(List.range p).map (reflect p) := by
    change (List.range p).reverse=(List.range p).map (fun x => p-1-x)
    have hr : (List.range' 0 p).reverse=(List.range p).map (fun x => 0+p-1-x) := List.reverse_range'
    simpa [List.range_eq_range'] using hr
  rw [←he]
  exact List.reverse_perm _

theorem complement_sums (p : Nat) (c : List Nat) (hb : ∀ x∈c,x<p) :
    edgeSums (c.map (reflect p))=(edgeSums c).map (reflect (2*p-1)) := by
  induction c using edgeSums.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b c ih =>
    have ha := hb a (by simp)
    have hbb := hb b (by simp)
    have ht : ∀ x∈b::c,x<p := by intro x hx; exact hb x (by simp [hx])
    change (reflect p a+reflect p b)::edgeSums ((b::c).map (reflect p)) =
      reflect (2*p-1) (a+b)::(edgeSums (b::c)).map (reflect (2*p-1))
    rw [ih ht]
    congr 1
    unfold reflect
    omega

theorem transform_boundary (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    BoundaryCore p (transform p c) := by
  have hp := hc.1
  have hlen := hc.2.1
  have heven : c.length%2=0 := by rw [hlen]; omega
  have sides := sides_reverse c
  simp only [heven,ite_true] at sides
  have hb := boundary_entries_small p c hc
  have hr : ∀ x∈c.reverse,x<p := by intro x hx; exact hb x (List.mem_reverse.mp hx)
  have hh : (highs (transform p c)).Perm (List.range p) := by
    unfold transform
    rw [highs_map,sides.1]
    exact (((List.reverse_perm (lows c)).trans hc.2.2.2.1).map (reflect p)).trans (reflect_range p)
  have hl : (lows (transform p c)).Perm (List.range p) := by
    unfold transform
    rw [lows_map,sides.2]
    exact (((List.reverse_perm (highs c)).trans hc.2.2.1).map (reflect p)).trans (reflect_range p)
  have hs : (edgeSums (transform p c)).Perm (List.range (2*p-1)) := by
    unfold transform
    rw [complement_sums p c.reverse hr,edgeSums_reverse]
    exact (((List.reverse_perm (edgeSums c)).trans hc.2.2.2.2.1).map (reflect (2*p-1))).trans (reflect_range (2*p-1))
  refine ⟨hp,by simp [transform,hlen],hh,hl,hs,?_,?_⟩
  · have last := hc.2.2.2.2.2.2
    have hlst : c.getLast?=some (p-4) := by rw [List.getLast?_eq_getElem?,hlen]; exact last
    rw [←List.head?_eq_getElem?]
    simp only [transform,List.head?_map,List.head?_reverse,hlst,Option.map_some]
    unfold reflect
    congr 1 <;> omega
  · rw [←show (transform p c).length=2*p by simp [transform,hlen]]
    rw [←List.getLast?_eq_getElem?]
    have first := hc.2.2.2.2.2.1
    have hfst : c.head?=some 3 := by rw [List.head?_eq_getElem?]; exact first
    simp only [transform,List.getLast?_map,List.getLast?_reverse,hfst,Option.map_some]
    unfold reflect
    congr 1 <;> omega

theorem transform_involution (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    transform p (transform p c)=c := by
  have hb := boundary_entries_small p c hc
  simp only [transform,List.map_reverse,List.reverse_reverse,List.map_map]
  have he : c.map (fun x => reflect p (reflect p x))=c.map id := by
    apply List.map_congr_left
    intro x hx
    have h := hb x hx
    unfold reflect
    dsimp only [id]
    omega
  simpa only [Function.comp_def,List.map_id] using he

theorem transform_lookup (p : Nat) (c : List Nat) (i : Nat)
    (hlen : c.length=2*p) (hi : i<2*p) :
    (transform p c)[2*p-1-i]?=c[i]?.map (reflect p) := by
  unfold transform
  rw [List.getElem?_map]
  have hr : c.reverse[2*p-1-i]?=c[i]? :=
    List.getElem?_reverse' (by rw [hlen]; omega)
  rw [hr]

theorem adjacent_zeros_coverage (p b d : Nat) (c : List Nat)
    (hc : BoundaryCore p c) (hb : 1≤b ∧ b+1≤2*p)
    (hzero : c[b-1]?=some 0) (hzero' : c[b]?=some 0)
    (hd : d=b ∨ d=b+1) : AllOdd.Coverage p d := by
  by_cases even : b%2=0
  · exact ⟨b,b+1,c,⟨hc,hb.1,by omega,even,by omega,hb.2,by omega,
      hzero,by simpa using hzero'⟩,hd⟩
  · refine ⟨b+1,b,c,⟨hc,by omega,hb.2,by omega,hb.1,by omega,by omega,
      by simpa using hzero',hzero⟩,?_⟩
    omega

end GracefulBoundary.ReverseComplement
