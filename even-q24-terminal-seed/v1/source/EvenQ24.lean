import Q24B4Positions
namespace GracefulBoundary.EvenQ24
open P20Q24

/-- Even counterpart of the q24 insertion state. -/
structure State (k z : Nat) (c : List Nat) : Prop where
  size : 26≤k
  even : k%2=0
  zeroInside : 1≤z ∧ z+2<k
  zeroOdd : z%2=1
  length : c.length=2*k+1
  high : (highs c).Perm (List.range (k+1))
  low : (lows c).Perm (List.range k)
  sums : (edgeSums c).Perm (List.range (2*k))
  midpoint : c[k]?=some k
  neighbor1 : c[z-1]?=some 1
  lowZero : c[z]?=some 0
  highZero : c[z+1]?=some 0
  neighbor2 : c[z+2]?=some 2
  terminal : c[2*k]?=some 12

theorem decomposition (k z : Nat) (c : List Nat) (h : State k z c) :
    c=c.take z ++ [0,0] ++ c.drop (z+2) :=
  split_two c z 0 0 h.lowZero h.highZero

theorem part_lengths (k z : Nat) (c : List Nat) (h : State k z c) :
    (c.take z).length=z ∧ (c.drop (z+2)).length=2*k-z-1 := by
  simp only [List.length_take,List.length_drop,h.length]
  have hi := h.zeroInside
  omega

theorem parts_positive (k z : Nat) (c : List Nat) (h : State k z c) :
    (∀ x∈c.take z,0<x) ∧ (∀ x∈c.drop (z+2),0<x) := by
  have hh := h.high.count_eq 0
  have hl := h.low.count_eq 0
  simp only [List.count_range,show 0<k+1 by have := h.size; omega,
    show 0<k by have := h.size; omega,ite_true] at hh hl
  have ht := count_sides 0 c
  have hz : c.count 0=2 := by omega
  rw [decomposition k z c h] at hz
  simp only [List.count_append] at hz
  simp at hz
  have hu : (c.take z).count 0=0 := by omega
  have hv : (c.drop (z+2)).count 0=0 := by omega
  constructor <;> intro x hx
  · have hn := List.not_mem_of_count_eq_zero hu
    by_cases he : x=0
    · subst x; exact False.elim (hn hx)
    · omega
  · have hn := List.not_mem_of_count_eq_zero hv
    by_cases he : x=0
    · subst x; exact False.elim (hn hx)
    · omega

theorem part_anchors (k z : Nat) (c : List Nat) (h : State k z c) :
    (c.take z).getLast?=some 1 ∧ (c.drop (z+2)).head?=some 2 ∧
    (c.drop (z+2)).getLast?=some 12 := by
  have hz := h.zeroInside
  have nonempty : z≠0 := by omega
  have before : ¬c.length≤z+2 := by rw [h.length]; omega
  refine ⟨?_,?_,?_⟩
  · simp [List.getLast?_take,nonempty,h.neighbor1]
  · simpa using h.neighbor2
  · rw [List.getLast?_drop]
    simp only [before,ite_false]
    rw [List.getLast?_eq_getElem?,h.length,show 2*k+1-1=2*k by omega]
    exact h.terminal

theorem extend_sides_B2 (k z : Nat) (c : List Nat) (h : State k z c) :
    (highs (P20Q24.extend z c)).Perm (List.range (k+25)) ∧
    (lows (P20Q24.extend z c)).Perm (List.range (k+24)) := by
  have lens := part_lengths k z c h
  have hp := parts_positive k z c h
  have odd : (c.take z).length%2=1 := by rw [lens.1]; exact h.zeroOdd
  have even : (c.drop (z+2)).length%2=0 := by rw [lens.2]; have := h.zeroOdd; omega
  have hh := P20Q24.surgery_high (c.take z) (c.drop (z+2)) odd even hp.1 hp.2
  have hl := P20Q24.surgery_low (c.take z) (c.drop (z+2)) odd even hp.1 hp.2
  rw [←decomposition k z c h] at hh hl
  have a : ((highs c).map bump24 ++ lows P20Q24.B ++ lows P20Q24.D ++ lows P20Q24.A).Perm
      ((List.range (k+1)).map bump24 ++ List.range' 1 24) := by
    simpa only [List.append_assoc] using (h.high.map bump24).append P20Q24.fresh_high
  have b : ((lows c).map bump24 ++ highs P20Q24.B ++ highs P20Q24.D ++ highs P20Q24.A).Perm
      ((List.range k).map bump24 ++ List.range' 1 24) := by
    simpa only [List.append_assoc] using (h.low.map bump24).append P20Q24.fresh_low
  exact ⟨hh.trans (a.trans (P20Q24.side_interval (k+1) (by have hk:=h.size; omega))),
    hl.trans (b.trans (P20Q24.side_interval k (by have hk:=h.size; omega)))⟩

theorem extend_sides_B4 (k z : Nat) (c : List Nat) (h : State k z c) :
    (highs (Q24B4.extend z c)).Perm (List.range (k+25)) ∧
    (lows (Q24B4.extend z c)).Perm (List.range (k+24)) := by
  have lens := part_lengths k z c h
  have hp := parts_positive k z c h
  have odd : (c.take z).length%2=1 := by rw [lens.1]; exact h.zeroOdd
  have even : (c.drop (z+2)).length%2=0 := by rw [lens.2]; have := h.zeroOdd; omega
  have hh := Q24B4.surgery_high (c.take z) (c.drop (z+2)) odd even hp.1 hp.2
  have hl := Q24B4.surgery_low (c.take z) (c.drop (z+2)) odd even hp.1 hp.2
  rw [←decomposition k z c h] at hh hl
  have a : ((highs c).map bump24 ++ lows Q24B4.B ++ lows Q24B4.D ++ lows Q24B4.A).Perm
      ((List.range (k+1)).map bump24 ++ List.range' 1 24) := by
    simpa only [List.append_assoc] using (h.high.map bump24).append Q24B4.fresh_high
  have b : ((lows c).map bump24 ++ highs Q24B4.B ++ highs Q24B4.D ++ highs Q24B4.A).Perm
      ((List.range k).map bump24 ++ List.range' 1 24) := by
    simpa only [List.append_assoc] using (h.low.map bump24).append Q24B4.fresh_low
  exact ⟨hh.trans (a.trans (P20Q24.side_interval (k+1) (by have hk:=h.size; omega))),
    hl.trans (b.trans (P20Q24.side_interval k (by have hk:=h.size; omega)))⟩

theorem extend_sums_B2 (k z : Nat) (c : List Nat) (h : State k z c) :
    (edgeSums (P20Q24.extend z c)).Perm (List.range (2*(k+24))) := by
  have anchors := part_anchors k z c h
  have old := (P20Q24.old_sums (c.take z) (c.drop (z+2)) anchors.1 anchors.2.1).symm.trans
    (show (edgeSums (c.take z++[0,0]++c.drop (z+2))).Perm (List.range (2*k)) by rw [←decomposition k z c h]; exact h.sums)
  have next := (P20Q24.surgery_sums (c.take z) (c.drop (z+2)) anchors.1 anchors.2.1 anchors.2.2).trans
    (P20Q24.enlarged_sums (2*k) (by have := h.size; omega) _ old)
  simpa only [P20Q24.extend,show 2*k+48=2*(k+24) by omega] using next

theorem extend_sums_B4 (k z : Nat) (c : List Nat) (h : State k z c) :
    (edgeSums (Q24B4.extend z c)).Perm (List.range (2*(k+24))) := by
  have anchors := part_anchors k z c h
  have old := (Q24B4.old_sums (c.take z) (c.drop (z+2)) anchors.1 anchors.2.1).symm.trans
    (show (edgeSums (c.take z++[0,0]++c.drop (z+2))).Perm (List.range (2*k)) by rw [←decomposition k z c h]; exact h.sums)
  have next := (Q24B4.surgery_sums (c.take z) (c.drop (z+2)) anchors.1 anchors.2.1 anchors.2.2).trans
    (Q24B4.enlarged_sums (2*k) (by have := h.size; omega) _ old)
  simpa only [Q24B4.extend,show 2*k+48=2*(k+24) by omega] using next

theorem extend_length_B2 (k z : Nat) (c : List Nat) (h : State k z c) :
    (P20Q24.extend z c).length=2*(k+24)+1 := by
  have lens := part_lengths k z c h
  have hk := h.size
  have hi := h.zeroInside
  simp only [P20Q24.extend,P20Q24.surgery,List.length_append,List.length_map,lens.1,lens.2,
    P20Q24.B,P20Q24.D,P20Q24.A,List.length_cons,List.length_nil]
  omega

theorem extend_length_B4 (k z : Nat) (c : List Nat) (h : State k z c) :
    (Q24B4.extend z c).length=2*(k+24)+1 := by
  have lens := part_lengths k z c h
  have hk := h.size
  have hi := h.zeroInside
  simp only [Q24B4.extend,Q24B4.surgery,List.length_append,List.length_map,lens.1,lens.2,
    Q24B4.B,Q24B4.D,Q24B4.A,List.length_cons,List.length_nil]
  omega

theorem extend_midpoint_B2 (k z : Nat) (c : List Nat) (h : State k z c) :
    (P20Q24.extend z c)[k+24]?=some (k+24) := by
  have lens := part_lengths k z c h
  have hi := h.zeroInside
  have bound : k-(z+2)<(c.drop (z+2)).length := by rw [lens.2]; omega
  have look := P20Q24.surgery_right_index (c.take z) (c.drop (z+2)) (k-(z+2)) bound
  have old : (c.drop (z+2))[k-(z+2)]?=some k := by
    rw [List.getElem?_drop,show z+2+(k-(z+2))=k by omega]
    exact h.midpoint
  rw [lens.1,show z+26+(k-(z+2))=k+24 by omega,old] at look
  simpa only [P20Q24.extend,Option.map_some] using look

theorem extend_midpoint_B4 (k z : Nat) (c : List Nat) (h : State k z c) :
    (Q24B4.extend z c)[k+24]?=some (k+24) := by
  have lens := part_lengths k z c h
  have hi := h.zeroInside
  have bound : k-(z+2)<(c.drop (z+2)).length := by rw [lens.2]; omega
  have look := Q24B4.surgery_right_index (c.take z) (c.drop (z+2)) (k-(z+2)) bound
  have old : (c.drop (z+2))[k-(z+2)]?=some k := by
    rw [List.getElem?_drop,show z+2+(k-(z+2))=k by omega]
    exact h.midpoint
  rw [lens.1,show z+26+(k-(z+2))=k+24 by omega,old] at look
  simpa only [Q24B4.extend,Option.map_some] using look

theorem extend_terminal_B2 (k z : Nat) (c : List Nat) (h : State k z c) :
    (P20Q24.extend z c)[2*(k+24)]?=some 12 := by
  have last : (P20Q24.extend z c).getLast?=some 12 := by
    simp only [P20Q24.extend,P20Q24.surgery,List.getLast?_append,
      show P20Q24.A.getLast?=some 12 by rfl]
    rfl
  rw [List.getLast?_eq_getElem?,extend_length_B2 k z c h,
    show 2*(k+24)+1-1=2*(k+24) by omega] at last
  exact last

theorem extend_terminal_B4 (k z : Nat) (c : List Nat) (h : State k z c) :
    (Q24B4.extend z c)[2*(k+24)]?=some 12 := by
  have last : (Q24B4.extend z c).getLast?=some 12 := by
    simp only [Q24B4.extend,Q24B4.surgery,List.getLast?_append,
      show Q24B4.A.getLast?=some 12 by rfl]
    rfl
  rw [List.getLast?_eq_getElem?,extend_length_B4 k z c h,
    show 2*(k+24)+1-1=2*(k+24) by omega] at last
  exact last

theorem extend_patch_B2 (k z : Nat) (c : List Nat) (h : State k z c) :
    (P20Q24.extend z c)[z+1]?=some 1 ∧ (P20Q24.extend z c)[z+2]?=some 0 ∧
    (P20Q24.extend z c)[z+3]?=some 0 ∧ (P20Q24.extend z c)[z+4]?=some 2 := by
  have lens := part_lengths k z c h
  have look (i : Nat) (hi : i<26) := P20Q24.surgery_patch_index (c.take z) (c.drop (z+2)) i hi
  have a := look 1 (by decide); have b := look 2 (by decide)
  have d := look 3 (by decide); have e := look 4 (by decide)
  simp only [lens.1] at a b d e
  exact ⟨by simpa [P20Q24.extend,P20Q24.B,P20Q24.D] using a,
    by simpa [P20Q24.extend,P20Q24.B,P20Q24.D] using b,
    by simpa [P20Q24.extend,P20Q24.B,P20Q24.D] using d,
    by simpa [P20Q24.extend,P20Q24.B,P20Q24.D] using e⟩

theorem extend_patch_B4 (k z : Nat) (c : List Nat) (h : State k z c) :
    (Q24B4.extend z c)[z+3]?=some 1 ∧ (Q24B4.extend z c)[z+4]?=some 0 ∧
    (Q24B4.extend z c)[z+5]?=some 0 ∧ (Q24B4.extend z c)[z+6]?=some 2 := by
  have lens := part_lengths k z c h
  have look (i : Nat) (hi : i<26) := Q24B4.surgery_patch_index (c.take z) (c.drop (z+2)) i hi
  have a := look 3 (by decide); have b := look 4 (by decide)
  have d := look 5 (by decide); have e := look 6 (by decide)
  simp only [lens.1] at a b d e
  exact ⟨by simpa [Q24B4.extend,Q24B4.B,Q24B4.D] using a,
    by simpa [Q24B4.extend,Q24B4.B,Q24B4.D] using b,
    by simpa [Q24B4.extend,Q24B4.B,Q24B4.D] using d,
    by simpa [Q24B4.extend,Q24B4.B,Q24B4.D] using e⟩

theorem q24_preserves_B2 (k z : Nat) (c : List Nat) (h : State k z c) :
    State (k+24) (z+2) (P20Q24.extend z c) := by
  have hk := h.size
  have hi := h.zeroInside
  have sides := extend_sides_B2 k z c h
  have patch := extend_patch_B2 k z c h
  refine ⟨by omega, by have := h.even; omega, ⟨by omega,by omega⟩, by have := h.zeroOdd; omega,
    extend_length_B2 k z c h, ?_,sides.2,extend_sums_B2 k z c h,?_,?_,patch.2.1,?_,?_,extend_terminal_B2 k z c h⟩
  · simpa only [show k+24+1=k+25 by omega] using sides.1
  · simpa only [show k+24=k+24 by rfl] using extend_midpoint_B2 k z c h
  · simpa only [show z+2-1=z+1 by omega] using patch.1
  · simpa only [show z+2+1=z+3 by omega] using patch.2.2.1
  · simpa only [show z+2+2=z+4 by omega] using patch.2.2.2

theorem q24_preserves_B4 (k z : Nat) (c : List Nat) (h : State k z c) :
    State (k+24) (z+4) (Q24B4.extend z c) := by
  have hk := h.size
  have hi := h.zeroInside
  have sides := extend_sides_B4 k z c h
  have patch := extend_patch_B4 k z c h
  refine ⟨by omega, by have := h.even; omega, ⟨by omega,by omega⟩, by have := h.zeroOdd; omega,
    extend_length_B4 k z c h, ?_,sides.2,extend_sums_B4 k z c h,?_,?_,patch.2.1,?_,?_,extend_terminal_B4 k z c h⟩
  · simpa only [show k+24+1=k+25 by omega] using sides.1
  · simpa only [show k+24=k+24 by rfl] using extend_midpoint_B4 k z c h
  · simpa only [show z+4-1=z+3 by omega] using patch.1
  · simpa only [show z+4+1=z+5 by omega] using patch.2.2.1
  · simpa only [show z+4+2=z+6 by omega] using patch.2.2.2

def evenSeed : List Nat := [14,7,6,6,1,0,0,2,4,4,5,5,9,13,13,18,16,19,23,23,25,22,22,17,19,24,26,25,24,21,20,20,18,14,11,16,21,12,17,11,8,15,15,9,7,10,10,8,3,1,2,3,12]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem evenSeed_state : State 26 5 evenSeed := by
  constructor <;> decide

def word : List Bool → List Nat
  | [] => evenSeed
  | b::bs => if b then Q24B4.extend (5+2*bs.length+2*bs.count true) (word bs)
             else P20Q24.extend (5+2*bs.length+2*bs.count true) (word bs)

theorem all_states (bs : List Bool) :
    State (26+24*bs.length) (5+2*bs.length+2*bs.count true) (word bs) := by
  induction bs with
  | nil => exact evenSeed_state
  | cons b bs ih =>
    cases b with
    | false =>
      have h := q24_preserves_B2 _ _ _ ih
      simpa [word,List.count_cons,
        show 26+24*bs.length+24=26+24*(bs.length+1) by omega,
        show 5+2*bs.length+2*bs.count true+2=5+2*(bs.length+1)+2*bs.count true by omega] using h
    | true =>
      have h := q24_preserves_B4 _ _ _ ih
      simpa [word,List.count_cons,
        show 26+24*bs.length+24=26+24*(bs.length+1) by omega,
        show 5+2*bs.length+2*bs.count true+4=5+2*(bs.length+1)+2*(bs.count true+1) by omega] using h


/-- The decoded even state is a midpoint-alpha certificate on the actual path graph. -/
theorem state_path_certificate (k z : Nat) (c : List Nat) (h : State k z c) :
    Graceful (pathGraph (2*k)) (2*k) (pathLabel (2*k) (coreLabels (2*k) c)) ∧
    Alpha (pathGraph (2*k)) (k-1) (pathLabel (2*k) (coreLabels (2*k) c)) ∧
    pathLabel (2*k) (coreLabels (2*k) c) ⟨k, by have hk := h.size; omega⟩ = k ∧
    pathLabel (2*k) (coreLabels (2*k) c) ⟨z, by have hk := h.size; have hiz := h.zeroInside.2; omega⟩ = 0 ∧
    pathLabel (2*k) (coreLabels (2*k) c) ⟨z+1, by have hk := h.size; have hiz := h.zeroInside.2; omega⟩ = 2*k := by
  have hk := h.size
  have hi := h.zeroInside
  have hh := h.high
  have hl := h.low
  have hs := h.sums
  have hp : (coreLabels (2*k) c).Perm (List.range (2*k+1)) := by
    simpa only [show 2*k+1=2*k+1 by rfl] using WholeTagged.tagged_labels k c hh hl
  have he : (edgeDiffs (coreLabels (2*k) c)).Perm (List.range' 1 (2*k)) :=
    WholeTagged.tagged_edges k c hh hl hs
  have hc : crosses (k-1) (coreLabels (2*k) c) :=
    WholeTagged.tagged_crosses k (by have := h.size; omega) c hh hl
  have hlen : (coreLabels (2*k) c).length=2*k+1 := by
    rw [coreLabels_length,h.length]
  have hmid : (coreLabels (2*k) c)[k]?=some k := by
    rw [coreLabels_lookup,h.midpoint]
    simp only [h.even,ite_true,Option.map_some]
    congr 1
    omega
  have hz : (coreLabels (2*k) c)[z]?=some 0 := by
    rw [coreLabels_lookup,h.lowZero]
    simp [h.zeroOdd]
  have hmax : (coreLabels (2*k) c)[z+1]?=some (2*k) := by
    rw [coreLabels_lookup,h.highZero]
    have hz := h.zeroOdd
    simp [show (z+1)%2=0 by omega]
  refine ⟨list_path_graceful (2*k) _ hp he,
    list_path_alpha (2*k) (k-1) _ hlen hc, ?_, ?_, ?_⟩
  · simp [pathLabel,hmid]
  · simp [pathLabel,hz]
  · simp [pathLabel,hmax]

/-- Reversing label bands preserves a bijection of a finite interval. -/
theorem complement_band {V : Type} (f : V → Nat) (M : Nat)
    (h : BandBijection f 0 M) : BandBijection (fun v => M-f v) 0 M := by
  constructor
  · intro v
    have hv := h.bounds v
    omega
  · intro v w he
    apply h.injective
    have hv := h.bounds v
    have hw := h.bounds w
    omega
  · intro x hx hM
    obtain ⟨v,hv⟩ := h.onto (M-x) (by omega) (by omega)
    refine ⟨v,?_⟩
    have hb := h.bounds v
    omega

theorem complement_graceful {V E : Type} (G : IndexedGraph V E) (M : Nat)
    (f : V → Nat) (h : Graceful G M f) :
    Graceful G M (fun v => M-f v) := by
  constructor
  · exact complement_band f M h.vertices
  · have heq : weight G (fun v => M-f v) = weight G f := by
      funext e
      simp only [weight,distance]
      have hs := h.vertices.bounds (G.source e)
      have ht := h.vertices.bounds (G.target e)
      omega
    rw [heq]
    exact h.edges

theorem complement_alpha_aux {V E : Type} (G : IndexedGraph V E) (M A B : Nat)
    (f : V → Nat) (hG : Graceful G M f) (hA : Alpha G A f)
    (hcut : B+A+1=M) : Alpha G B (fun v => M-f v) := by
  intro e
  change ((M-f (G.source e) ≤ B ∧ B < M-f (G.target e)) ∨
    (M-f (G.target e) ≤ B ∧ B < M-f (G.source e)))
  have hs := hG.vertices.bounds (G.source e)
  have ht := hG.vertices.bounds (G.target e)
  rcases hA e with h | h
  · right
    constructor <;> omega
  · left
    constructor <;> omega

theorem complement_alpha {V E : Type} (G : IndexedGraph V E) (M A : Nat)
    (f : V → Nat) (hG : Graceful G M f) (hA : Alpha G A f) (hA' : A<M) :
    Alpha G (M-A-1) (fun v => M-f v) := by
  apply complement_alpha_aux G M A (M-A-1) f hG hA
  omega

/-- The maximum endpoint at depth k-z becomes a zero under label complement. -/
theorem state_path_complement_certificate (k z : Nat) (c : List Nat) (h : State k z c) :
    Graceful (pathGraph (2*k)) (2*k)
      (fun v => 2*k - pathLabel (2*k) (coreLabels (2*k) c) v) ∧
    Alpha (pathGraph (2*k)) k
      (fun v => 2*k - pathLabel (2*k) (coreLabels (2*k) c) v) ∧
    (fun v => 2*k - pathLabel (2*k) (coreLabels (2*k) c) v) ⟨k, by have hk := h.size; omega⟩ = k ∧
    (fun v => 2*k - pathLabel (2*k) (coreLabels (2*k) c) v) ⟨z+1, by have hk := h.size; have hiz := h.zeroInside.2; omega⟩ = 0 := by
  have hi := h.zeroInside
  obtain ⟨hg,ha,hm,hz,hx⟩ := state_path_certificate k z c h
  have hm' : 2*k - pathLabel (2*k) (coreLabels (2*k) c) ⟨k, by omega⟩ = k := by omega
  have hx' : 2*k - pathLabel (2*k) (coreLabels (2*k) c) ⟨z+1, by omega⟩ = 0 := by omega
  have halpha := complement_alpha _ _ _ _ hg ha (by have := h.size; omega)
  have hcut : 2*k-(k-1)-1=k := by have := h.size; omega
  exact ⟨complement_graceful _ _ _ hg,
    by simpa only [hcut] using halpha,hm',hx'⟩


theorem window_arithmetic (t d : Nat) (hlo : 20+20*t≤d) (hhi : d≤21+22*t) :
    ∃ j, j≤t ∧ (d=21+22*t-2*j ∨ d=20+22*t-2*j) := by
  let q := 21+22*t-d
  have hq0 : 0≤q := by dsimp [q]; omega
  have hq1 : q≤2*t+1 := by dsimp [q]; omega
  have hmod : q%2<2 := Nat.mod_lt q (by decide)
  have hdiv : q=2*(q/2)+q%2 := by omega
  have hmodcases : q%2=0 ∨ q%2=1 := by omega
  refine ⟨q/2, ?_, ?_⟩
  · dsimp [q]
    omega
  · rcases hmodcases with hm | hm
    · left
      dsimp [q] at hdiv
      rw [hm] at hdiv
      dsimp [q]
      omega
    · right
      dsimp [q] at hdiv
      rw [hm] at hdiv
      dsimp [q]
      omega

/-- A concrete mixed B2/B4 history for each number of B4 steps. -/
def mixedHistory (t j : Nat) : List Bool :=
  List.replicate (t-j) false ++ List.replicate j true

theorem mixedHistory_length (t j : Nat) (hj : j≤t) : (mixedHistory t j).length=t := by
  simp [mixedHistory]
  omega

theorem mixedHistory_count (t j : Nat) : (mixedHistory t j).count true=j := by
  simp [mixedHistory,List.count_replicate]

/-- Every integer depth in the requested K=26+24t window has an actual
midpoint-alpha path certificate with a separately zeroed vertex at that depth. -/
theorem window_path_certificate (t d : Nat) (hlo : 20+20*t≤d) (hhi : d≤21+22*t) :
    ∃ j, j≤t ∧ ∃ c, State (26+24*t) (5+2*t+2*j) c ∧
      ((d=21+22*t-2*j ∧ ∃ v : Fin (2*(26+24*t)+1),
          v.val=5+2*t+2*j ∧
          Graceful (pathGraph (2*(26+24*t))) (2*(26+24*t))
            (pathLabel (2*(26+24*t)) (coreLabels (2*(26+24*t)) c)) ∧
          Alpha (pathGraph (2*(26+24*t))) ((26+24*t)-1)
            (pathLabel (2*(26+24*t)) (coreLabels (2*(26+24*t)) c)) ∧
          pathLabel (2*(26+24*t)) (coreLabels (2*(26+24*t)) c) v=0) ∨
       (d=20+22*t-2*j ∧ ∃ v : Fin (2*(26+24*t)+1),
          v.val=5+2*t+2*j+1 ∧
          Graceful (pathGraph (2*(26+24*t))) (2*(26+24*t))
            (fun v => 2*(26+24*t) - pathLabel (2*(26+24*t)) (coreLabels (2*(26+24*t)) c) v) ∧
          Alpha (pathGraph (2*(26+24*t))) (26+24*t)
            (fun v => 2*(26+24*t) - pathLabel (2*(26+24*t)) (coreLabels (2*(26+24*t)) c) v) ∧
          (fun v => 2*(26+24*t) - pathLabel (2*(26+24*t)) (coreLabels (2*(26+24*t)) c) v) v=0)) := by
  obtain ⟨j,hj,hwhich⟩ := window_arithmetic t d hlo hhi
  let c := word (mixedHistory t j)
  have hlen := mixedHistory_length t j hj
  have hcount := mixedHistory_count t j
  have hstate : State (26+24*t) (5+2*t+2*j) c := by
    dsimp [c]
    simpa [hlen,hcount] using all_states (mixedHistory t j)
  refine ⟨j,hj,c,hstate,?_⟩
  rcases hwhich with hd | hd
  · left
    have cert := state_path_certificate (26+24*t) (5+2*t+2*j) c hstate
    have hv : 5+2*t+2*j < 2*(26+24*t)+1 := by
      have hiz := hstate.zeroInside.2
      have hk := hstate.size
      omega
    refine ⟨hd,⟨⟨5+2*t+2*j,hv⟩,rfl,cert.1,cert.2.1,cert.2.2.2.1⟩⟩
  · right
    have cert := state_path_complement_certificate (26+24*t) (5+2*t+2*j) c hstate
    have hv : 5+2*t+2*j+1 < 2*(26+24*t)+1 := by
      have hiz := hstate.zeroInside.2
      have hk := hstate.size
      omega
    exact ⟨hd,⟨⟨5+2*t+2*j+1,hv⟩,rfl,cert.1,cert.2.1,cert.2.2.2⟩⟩

end GracefulBoundary.EvenQ24
