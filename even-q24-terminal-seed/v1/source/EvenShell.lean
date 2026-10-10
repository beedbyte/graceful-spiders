import EvenIdentification

namespace GracefulBoundary.Even

def GenericPathCertificate (p : Nat) (c : List Nat) : Prop :=
  c.length=4*p+9 ∧ c.Perm (List.range (4*p+9)) ∧
  (edgeDiffs c).Perm (List.range' 1 (4*p+8)) ∧
  crosses (2*p+4) c ∧ c[2*p+4]?=some (2*p+4)

theorem core_difference (p a b : Nat) (ha : a<p) (hb : b<p) :
    distance (4*p+8-a) b=4*p+8-(a+b) := by
  unfold distance
  omega

theorem decode_core_edge_values (p : Nat) (c : List Nat) (high : Bool)
    (hc : ∀ x ∈ c, x < p) :
    edgeDiffs (decode (4*p+8) high c)=
      (edgeSums c).map (fun q => 4*p+8-q) := by
  induction c using edgeSums.induct generalizing high with
  | case1 => rfl
  | case2 a => cases high <;> rfl
  | case3 a b xs ih =>
    have ha : a < p := hc a (by simp)
    have hb : b < p := hc b (by simp)
    have htail : ∀ x ∈ b::xs, x<p := by intro x hx; exact hc x (by simp [hx])
    cases high with
    | false =>
      change distance a (4*p+8-b) :: edgeDiffs (decode (4*p+8) true (b::xs)) = _
      rw [ih true htail]
      simp only [edgeSums,List.map_cons]
      congr 1
      rw [distance_comm,core_difference p b a hb ha]
      congr 1; omega
    | true =>
      change distance (4*p+8-a) b :: edgeDiffs (decode (4*p+8) false (b::xs)) = _
      rw [ih false htail]
      simp only [edgeSums,List.map_cons]
      congr 1
      exact core_difference p a b ha hb

theorem reflected_range (p : Nat) (hp : 1 ≤ p) :
    ((List.range p).map (fun x => 4*p+8-x)).Perm (List.range' (3*p+9) p) := by
  have h : (List.range' (3*p+9) p).reverse=(List.range p).map (fun x => 4*p+8-x) := by
    rw [List.reverse_range',show 3*p+9+p-1=4*p+8 by omega]
  rw [← h]
  exact List.reverse_perm _

theorem decoded_core_labels (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    (coreLabels (4*p+8) c).Perm (List.range' (3*p+9) p ++ List.range p) := by
  rcases hc with ⟨hp,_,hh,hl,_⟩
  rw [coreLabels_decode]
  exact (decode_side_permutations (4*p+8) c).1.trans
    (((List.Perm.map (fun x => 4*p+8-x) hh).trans (reflected_range p (by omega))).append hl)

def oppositePairs (p : Nat) := (List.range p).flatMap (fun j => [2*p+5+j,2*p+3-j])

theorem opposite_pairs_labels (p : Nat) (hp : 1 ≤ p) :
    (oppositePairs p).Perm (List.range' (2*p+5) p ++ List.range' (p+4) p) := by
  have h := pairs_perm (List.range p) (fun j => 2*p+5+j) (fun j => 2*p+3-j)
  have hh : (List.range p).map (fun j => 2*p+5+j) = List.range' (2*p+5) p :=
    List.range'_eq_map_range.symm
  have hl : (List.range' (p+4) p).reverse=(List.range p).map (fun j => 2*p+3-j) := by
    rw [List.reverse_range',show p+4+p-1=2*p+3 by omega]
  rw [hh,← hl] at h
  exact h.trans ((List.Perm.refl _).append (List.reverse_perm _))

def selectedArm (p : Nat) (c : List Nat) := coreLabels (4*p+8) c ++ [3*p+5,p+2,3*p+7,p+3]

def oppositeArm (p : Nat) := oppositePairs p ++ [3*p+6,p,3*p+8,p+1]

def completePath (p : Nat) (c : List Nat) :=
  (selectedArm p c).reverse ++ [2*p+4] ++ oppositeArm p

def shellLabelBands (p : Nat) :=
  (List.range' (3*p+9) p ++ List.range p ++ [3*p+5,p+2,3*p+7,p+3]) ++
  [2*p+4] ++ (List.range' (2*p+5) p ++ List.range' (p+4) p) ++ [3*p+6,p,3*p+8,p+1]

theorem shell_labels_partition (p : Nat) (hp : 1 ≤ p) :
    (shellLabelBands p).Perm (List.range (4*p+9)) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [shellLabelBands,List.count_append,List.count_cons,List.count_nil,
    count_band,List.count_range,Nat.beq_eq_true_eq]
  repeat (any_goals (first | omega | split))

theorem complete_path_labels (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    (completePath p c).Perm (List.range (4*p+9)) := by
  have hcore := (decoded_core_labels p c hc).append (List.Perm.refl [3*p+5,p+2,3*p+7,p+3])
  have hleft := (List.reverse_perm (coreLabels (4*p+8) c ++ [3*p+5,p+2,3*p+7,p+3])).trans hcore
  have hp := hc.1
  have hpair := opposite_pairs_labels p (by omega)
  have h := ((hleft.append (List.Perm.refl [2*p+4])).append hpair).append
    (List.Perm.refl [3*p+6,p,3*p+8,p+1])
  simpa only [completePath,selectedArm,oppositeArm,List.append_assoc] using
    h.trans (shell_labels_partition p (by omega))

theorem decoded_core_boundaries (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    (coreLabels (4*p+8) c).head?=some (4*p+5) ∧
    (coreLabels (4*p+8) c).getLast?=some (p-4) := by
  rcases hc with ⟨hp,hlen,_,_,_,hf,ht⟩
  constructor
  · rw [List.head?_eq_getElem?,coreLabels_lookup,hf]
    simp
  · rw [List.getLast?_eq_getElem?,coreLabels_length,hlen,coreLabels_lookup,ht]
    simp [show ¬ (2*p-1)%2=0 by omega]

theorem selected_arm_differences (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    edgeDiffs ((2*p+4)::selectedArm p c) =
      [2*p+1] ++ (edgeSums c).map (fun q => 4*p+8-q) ++ [2*p+9,2*p+3,2*p+5,2*p+4] := by
  have hp := hc.1
  have hb := decoded_core_boundaries p c hc
  obtain ⟨tail,htail⟩ := List.head?_eq_some_iff.mp hb.1
  have hstart : edgeDiffs ((2*p+4)::selectedArm p c) =
      distance (2*p+4) (4*p+5) :: edgeDiffs (selectedArm p c) := by
    simp only [selectedArm,htail,List.cons_append,edgeDiffs]
  rw [hstart]
  unfold selectedArm
  rw [edgeDiffs_join _ (p-4) (3*p+5) [p+2,3*p+7,p+3] hb.2]
  rw [coreLabels_decode,decode_core_edge_values p c true (boundary_entries_small p c hc)]
  simp only [edgeDiffs,List.cons_append,List.nil_append]
  have h0 : distance (2*p+4) (4*p+5)=2*p+1 := by unfold distance; omega
  have h1 : distance (p-4) (3*p+5)=2*p+9 := by unfold distance; omega
  have h2 : distance (3*p+5) (p+2)=2*p+3 := by unfold distance; omega
  have h3 : distance (p+2) (3*p+7)=2*p+5 := by unfold distance; omega
  have h4 : distance (3*p+7) (p+3)=2*p+4 := by unfold distance; omega
  simp [h0,h1,h2,h3,h4]

def pairBlock (p j n : Nat) := (List.range' j n).flatMap (fun i => [2*p+5+i,2*p+3-i])

theorem pair_block_differences (p j n : Nat) (tail : List Nat) (h : j+n ≤ p) :
    edgeDiffs ((2*p+4-j)::(pairBlock p j n ++ tail)) =
      List.range' (2*j+1) (2*n) ++ edgeDiffs ((2*p+4-(j+n))::tail) := by
  induction n generalizing j with
  | zero => simp [pairBlock]
  | succ n ih =>
    have hnext : j+1+n ≤ p := by omega
    have hlow : 2*p+3-j=2*p+4-(j+1) := by omega
    have h1 : distance (2*p+4-j) (2*p+5+j)=2*j+1 := by unfold distance; omega
    have h2 : distance (2*p+5+j) (2*p+3-j)=2*j+2 := by unfold distance; omega
    simp only [pairBlock,List.range'_succ,List.flatMap_cons,List.cons_append,List.nil_append]
    change distance (2*p+4-j) (2*p+5+j) :: distance (2*p+5+j) (2*p+3-j) ::
      edgeDiffs ((2*p+3-j)::(pairBlock p (j+1) n ++ tail)) = _
    rw [h1,h2,hlow,ih (j+1) hnext]
    rw [show 2*(n+1)=2*n+1+1 by omega,List.range'_succ,List.range'_succ]
    simp only [List.cons_append]
    congr 3
    simp [Nat.add_comm,Nat.add_left_comm]

theorem opposite_arm_differences (p : Nat) :
    edgeDiffs ((2*p+4)::oppositeArm p) =
      List.range' 1 (2*p) ++ [2*p+2,2*p+6,2*p+8,2*p+7] := by
  have h := pair_block_differences p 0 p [3*p+6,p,3*p+8,p+1] (by omega)
  have hlow : 2*p+4-p=p+4 := by omega
  have h1 : distance (p+4) (3*p+6)=2*p+2 := by unfold distance; omega
  have h2 : distance (3*p+6) p=2*p+6 := by unfold distance; omega
  have h3 : distance p (3*p+8)=2*p+8 := by unfold distance; omega
  have h4 : distance (3*p+8) (p+1)=2*p+7 := by unfold distance; omega
  simpa [oppositeArm,oppositePairs,pairBlock,List.range_eq_range',hlow,edgeDiffs,h1,h2,h3,h4] using h

theorem full_path_edge_decomposition (p : Nat) (c : List Nat) :
    edgeDiffs (completePath p c)=
      (edgeDiffs ((2*p+4)::selectedArm p c)).reverse ++
      edgeDiffs ((2*p+4)::oppositeArm p) := by
  have hshape : completePath p c=(selectedArm p c).reverse ++ (2*p+4)::oppositeArm p := by
    simp [completePath,selectedArm,oppositeArm,oppositePairs,List.append_assoc]
  rw [hshape,edgeDiffs_overlap]
  have hr : (selectedArm p c).reverse ++ [2*p+4]=((2*p+4)::selectedArm p c).reverse := by simp
  rw [hr,edgeDiffs_reverse]

theorem reflected_sums (p : Nat) (hp : 4≤p) :
    ((List.range (2*p-1)).map (fun q => 4*p+8-q)).Perm (List.range' (2*p+10) (2*p-1)) := by
  have h : (List.range' (2*p+10) (2*p-1)).reverse=
      (List.range (2*p-1)).map (fun q => 4*p+8-q) := by
    rw [List.reverse_range',show 2*p+10+(2*p-1)-1=4*p+8 by omega]
  rw [←h]
  exact List.reverse_perm _

set_option maxHeartbeats 3000000 in
theorem complete_path_differences (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    (edgeDiffs (completePath p c)).Perm (List.range' 1 (4*p+8)) := by
  rw [full_path_edge_decomposition,selected_arm_differences p c hc,opposite_arm_differences]
  have hs := (List.Perm.map (fun q => 4*p+8-q) hc.2.2.2.2.1).trans (reflected_sums p hc.1)
  apply List.perm_iff_count.mpr
  intro x
  have hx := hs.count_eq x
  have hp := hc.1
  simp only [List.count_append,List.count_reverse,List.count_cons,List.count_nil,
    count_band,Nat.beq_eq_true_eq] at hx ⊢
  rw [hx]
  repeat (any_goals (first | omega | split))

theorem decoded_core_crosses (p : Nat) (c : List Nat) (high : Bool)
    (hc : ∀ x ∈ c, x<p) : crosses (2*p+4) (decode (4*p+8) high c) := by
  induction c using edgeSums.induct generalizing high with
  | case1 => trivial
  | case2 a => cases high <;> trivial
  | case3 a b xs ih =>
    have ha := hc a (by simp)
    have hb := hc b (by simp)
    have ht : ∀ x ∈ b::xs, x<p := by intro x hx; exact hc x (by simp [hx])
    cases high with
    | false =>
      change cross (2*p+4) a (4*p+8-b) ∧ crosses (2*p+4) (decode (4*p+8) true (b::xs))
      exact ⟨Or.inl ⟨by omega,by omega⟩,ih true ht⟩
    | true =>
      change cross (2*p+4) (4*p+8-a) b ∧ crosses (2*p+4) (decode (4*p+8) false (b::xs))
      exact ⟨Or.inr ⟨by omega,by omega⟩,ih false ht⟩

theorem selected_arm_crosses (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    crosses (2*p+4) ((2*p+4)::selectedArm p c) := by
  have hp := hc.1
  have hb := decoded_core_boundaries p c hc
  have hcore : crosses (2*p+4) (coreLabels (4*p+8) c) := by
    rw [coreLabels_decode]
    exact decoded_core_crosses p c true (boundary_entries_small p c hc)
  have htail : crosses (2*p+4) [3*p+5,p+2,3*p+7,p+3] := by simp [crosses]; omega
  have hab : cross (2*p+4) (p-4) (3*p+5) := Or.inl ⟨by omega,by omega⟩
  have harm := crosses_join (2*p+4) (coreLabels (4*p+8) c) (p-4) (3*p+5) [p+2,3*p+7,p+3] hcore htail hb.2 hab
  have hhead : (selectedArm p c).head?=some (4*p+5) := by
    simp [selectedArm,List.head?_append,hb.1]
  exact crosses_prepend (2*p+4) (2*p+4) (4*p+5) (selectedArm p c) harm hhead
    (Or.inl ⟨by omega,by omega⟩)

theorem pair_block_crosses (p j n : Nat) (tail : List Nat) (h : j+n ≤ p)
    (htail : crosses (2*p+4) ((2*p+4-(j+n))::tail)) :
    crosses (2*p+4) ((2*p+4-j)::(pairBlock p j n ++ tail)) := by
  induction n generalizing j with
  | zero => simpa [pairBlock] using htail
  | succ n ih =>
    have hnext : j+1+n ≤ p := by omega
    have hlow : 2*p+3-j=2*p+4-(j+1) := by omega
    have htail' : crosses (2*p+4) ((2*p+4-(j+1+n))::tail) := by
      simpa [Nat.add_comm,Nat.add_left_comm] using htail
    have hi := ih (j+1) hnext htail'
    simp only [pairBlock,List.range'_succ,List.flatMap_cons,List.cons_append,List.nil_append]
    change cross (2*p+4) (2*p+4-j) (2*p+5+j) ∧
      cross (2*p+4) (2*p+5+j) (2*p+3-j) ∧
      crosses (2*p+4) ((2*p+3-j)::(pairBlock p (j+1) n ++ tail))
    refine ⟨Or.inl ⟨by omega,by omega⟩,Or.inr ⟨by omega,by omega⟩,?_⟩
    rw [hlow]
    exact hi

theorem opposite_arm_crosses (p : Nat) : crosses (2*p+4) ((2*p+4)::oppositeArm p) := by
  have ht : crosses (2*p+4) ((2*p+4-(0+p))::[3*p+6,p,3*p+8,p+1]) := by
    simp [crosses]; omega
  have h := pair_block_crosses p 0 p [3*p+6,p,3*p+8,p+1] (by omega) ht
  simpa [oppositeArm,oppositePairs,pairBlock,List.range_eq_range'] using h

theorem complete_path_crosses (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    crosses (2*p+4) (completePath p c) := by
  have hleft := crosses_reverse (2*p+4) ((2*p+4)::selectedArm p c) (selected_arm_crosses p c hc)
  have hright := opposite_arm_crosses p
  have hshape : completePath p c=(selectedArm p c).reverse ++ (2*p+4)::oppositeArm p := by
    simp [completePath,selectedArm,oppositeArm,oppositePairs,List.append_assoc]
  rw [hshape]
  exact crosses_overlap (2*p+4) (selectedArm p c).reverse (2*p+4) (oppositeArm p)
    (by simpa using hleft) hright

theorem selected_arm_length (p : Nat) (c : List Nat) (hlen : c.length=2*p) :
    (selectedArm p c).length=2*p+4 := by simp [selectedArm,coreLabels,hlen]

theorem complete_path_midpoint (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    (completePath p c)[2*p+4]?=some (2*p+4) := by
  have hlen := selected_arm_length p c hc.2.1
  have hshape : completePath p c=(selectedArm p c).reverse ++ (2*p+4)::oppositeArm p := by
    simp [completePath,selectedArm,oppositeArm,oppositePairs,List.append_assoc]
  rw [hshape,List.getElem?_append_right (by simp [hlen])]
  simp [hlen]

theorem boundary_shell_bridge (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    GenericPathCertificate p (completePath p c) := by
  have hv := complete_path_labels p c hc
  refine ⟨?_,hv,complete_path_differences p c hc,complete_path_crosses p c hc,
    complete_path_midpoint p c hc⟩
  simpa using hv.length_eq

theorem complete_path_core_lookup (p : Nat) (c : List Nat) (i : Nat)
    (hlen : c.length=2*p) (hi : i < 2*p) :
    (completePath p c)[2*p+3-i]?=(coreLabels (4*p+8) c)[i]? := by
  have ha := selected_arm_length p c hlen
  have hshape : completePath p c=(selectedArm p c).reverse ++ (2*p+4)::oppositeArm p := by
    simp [completePath,selectedArm,oppositeArm,oppositePairs,List.append_assoc]
  rw [hshape,List.getElem?_append_left (by simp [ha]; omega)]
  have hr : ((selectedArm p c).reverse)[2*p+3-i]?=(selectedArm p c)[i]? :=
    List.getElem?_reverse' (by rw [ha]; omega)
  rw [hr]
  unfold selectedArm
  rw [List.getElem?_append_left (by rw [coreLabels_length,hlen]; exact hi)]

end GracefulBoundary.Even
