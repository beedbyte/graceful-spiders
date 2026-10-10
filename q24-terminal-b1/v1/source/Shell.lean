import Recurrence
namespace GracefulBoundary

def decode (M : Nat) (high : Bool) : List Nat → List Nat
  | [] => []
  | a::xs => (if high then M-a else a) :: decode M (!high) xs

theorem decode_zipIdx (M : Nat) (c : List Nat) (j : Nat) :
    (c.zipIdx j).map (fun (x,i) => if i%2=0 then M-x else x) =
      decode M (decide (j%2=0)) c := by
  induction c generalizing j with
  | nil => rfl
  | cons a c ih =>
    rw [List.zipIdx_cons,List.map_cons,ih]
    have hflip : decide ((j+1)%2=0) = !(decide (j%2=0)) := by
      by_cases hj : j%2=0
      · simp [hj,show ¬ (j+1)%2=0 by omega]
      · simp [hj,show (j+1)%2=0 by omega]
    simp [decode,hflip]

theorem coreLabels_decode (M : Nat) (c : List Nat) : coreLabels M c=decode M true c := by
  exact decode_zipIdx M c 0

theorem decode_side_permutations (M : Nat) (c : List Nat) :
    (decode M true c).Perm ((highs c).map (fun x => M-x) ++ lows c) ∧
    (decode M false c).Perm (highs c ++ (lows c).map (fun x => M-x)) := by
  induction c with
  | nil => simp [decode,highs,lows]
  | cons a c ih =>
    constructor <;> apply List.perm_iff_count.mpr <;> intro x
    · have ht := ih.2.count_eq x
      simp [decode,List.count_cons] at ht ⊢
      omega
    · have ht := ih.1.count_eq x
      simp [decode,List.count_cons] at ht ⊢
      omega

theorem boundary_entries_small (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    ∀ x ∈ c, x < p := by
  rcases hc with ⟨_,_,hh,hl,_⟩
  intro x hx
  have hcount := count_sides x c
  have hz : 0 < c.count x := List.count_pos_iff.mpr hx
  have hhigh := hh.count_eq x
  have hlow := hl.count_eq x
  simp only [List.count_range] at hhigh hlow
  by_cases hxp : x<p
  · exact hxp
  · simp only [hxp,ite_false] at hhigh hlow
    omega

theorem decode_core_edge_values (p : Nat) (c : List Nat) (high : Bool)
    (hc : ∀ x ∈ c, x < p) :
    edgeDiffs (decode (4*p+6) high c)=
      (edgeSums c).map (fun q => 4*p+6-q) := by
  induction c using edgeSums.induct generalizing high with
  | case1 => rfl
  | case2 a => cases high <;> rfl
  | case3 a b xs ih =>
    have ha : a < p := hc a (by simp)
    have hb : b < p := hc b (by simp)
    have htail : ∀ x ∈ b::xs, x<p := by intro x hx; exact hc x (by simp [hx])
    cases high with
    | false =>
      change distance a (4*p+6-b) :: edgeDiffs (decode (4*p+6) true (b::xs)) = _
      rw [ih true htail]
      simp only [edgeSums,List.map_cons]
      congr 1
      rw [distance_comm,core_difference p b a hb ha]
      congr 1; omega
    | true =>
      change distance (4*p+6-a) b :: edgeDiffs (decode (4*p+6) false (b::xs)) = _
      rw [ih false htail]
      simp only [edgeSums,List.map_cons]
      congr 1
      exact core_difference p a b ha hb

theorem reflected_range (p : Nat) (hp : 1 ≤ p) :
    ((List.range p).map (fun x => 4*p+6-x)).Perm (List.range' (3*p+7) p) := by
  have h : (List.range' (3*p+7) p).reverse=(List.range p).map (fun x => 4*p+6-x) := by
    rw [List.reverse_range',show 3*p+7+p-1=4*p+6 by omega]
  rw [← h]
  exact List.reverse_perm _

theorem decoded_core_labels (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    (coreLabels (4*p+6) c).Perm (List.range' (3*p+7) p ++ List.range p) := by
  rcases hc with ⟨hp,_,hh,hl,_⟩
  rw [coreLabels_decode]
  exact (decode_side_permutations (4*p+6) c).1.trans
    (((List.Perm.map (fun x => 4*p+6-x) hh).trans (reflected_range p (by omega))).append hl)

theorem pairs_perm (xs : List Nat) (f g : Nat → Nat) :
    (xs.flatMap (fun j => [f j,g j])).Perm (xs.map f ++ xs.map g) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    apply List.perm_iff_count.mpr
    intro a
    have ht := ih.count_eq a
    simp [List.count_cons] at ht ⊢
    omega

def oppositePairs (p : Nat) := (List.range p).flatMap (fun j => [2*p+3+j,2*p+1-j])

theorem opposite_pairs_labels (p : Nat) (hp : 1 ≤ p) :
    (oppositePairs p).Perm (List.range' (2*p+3) p ++ List.range' (p+2) p) := by
  have h := pairs_perm (List.range p) (fun j => 2*p+3+j) (fun j => 2*p+1-j)
  have hh : (List.range p).map (fun j => 2*p+3+j) = List.range' (2*p+3) p :=
    List.range'_eq_map_range.symm
  have hl : (List.range' (p+2) p).reverse=(List.range p).map (fun j => 2*p+1-j) := by
    rw [List.reverse_range',show p+2+p-1=2*p+1 by omega]
  rw [hh,← hl] at h
  exact h.trans ((List.Perm.refl _).append (List.reverse_perm _))

def shellLabelBands (p : Nat) :=
  (List.range' (3*p+7) p ++ List.range p ++ [3*p+3,p+1,3*p+4]) ++
  [2*p+2] ++ (List.range' (2*p+3) p ++ List.range' (p+2) p) ++ [3*p+6,p,3*p+5]

set_option maxHeartbeats 3000000 in
theorem shell_labels_partition (p : Nat) (hp : 1 ≤ p) :
    (shellLabelBands p).Perm (List.range (4*p+7)) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [shellLabelBands,List.count_append,List.count_cons,List.count_nil,
    count_band,List.count_range,Nat.beq_eq_true_eq]
  repeat (any_goals (first | omega | split))

theorem complete_path_labels (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    (completePath p c).Perm (List.range (4*p+7)) := by
  have hcore := (decoded_core_labels p c hc).append (List.Perm.refl [3*p+3,p+1,3*p+4])
  have hleft := (List.reverse_perm (coreLabels (4*p+6) c ++ [3*p+3,p+1,3*p+4])).trans hcore
  have hp := hc.1
  have hpair := opposite_pairs_labels p (by omega)
  have h := ((hleft.append (List.Perm.refl [2*p+2])).append hpair).append
    (List.Perm.refl [3*p+6,p,3*p+5])
  exact h.trans (shell_labels_partition p (by omega))


theorem coreLabels_lookup (M : Nat) (c : List Nat) (i : Nat) :
    (coreLabels M c)[i]?=c[i]?.map (fun x => if i%2=0 then M-x else x) := by
  simp [coreLabels,List.getElem?_zipIdx,Option.map_map,Function.comp_def]

theorem coreLabels_length (M : Nat) (c : List Nat) : (coreLabels M c).length=c.length := by
  simp [coreLabels]

theorem decoded_core_boundaries (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    (coreLabels (4*p+6) c).head?=some (4*p+3) ∧
    (coreLabels (4*p+6) c).getLast?=some (p-4) := by
  rcases hc with ⟨hp,hlen,_,_,_,hf,ht⟩
  constructor
  · rw [List.head?_eq_getElem?,coreLabels_lookup,hf]
    simp
  · rw [List.getLast?_eq_getElem?,coreLabels_length,hlen,coreLabels_lookup,ht]
    simp [show ¬ (2*p-1)%2=0 by omega]

theorem edgeDiffs_join (u : List Nat) (a b : Nat) (v : List Nat) (hu : u.getLast?=some a) :
    edgeDiffs (u++b::v)=edgeDiffs u ++ distance a b :: edgeDiffs (b::v) := by
  induction u with
  | nil => simp at hu
  | cons x u ih =>
    cases u with
    | nil => simp at hu; subst x; rfl
    | cons y u =>
      have ht : (y::u).getLast?=some a := by simpa using hu
      simpa only [List.cons_append,edgeDiffs,List.cons_append] using congrArg (List.cons (distance x y)) (ih ht)

theorem edgeDiffs_overlap (u : List Nat) (a : Nat) (v : List Nat) :
    edgeDiffs (u++a::v)=edgeDiffs (u++[a]) ++ edgeDiffs (a::v) := by
  induction u with
  | nil => simp [edgeDiffs]
  | cons b u ih =>
    cases u with
    | nil => simp [edgeDiffs]
    | cons d u => simpa only [List.cons_append,edgeDiffs,List.cons_append] using congrArg (List.cons (distance b d)) ih

theorem edgeDiffs_reverse (c : List Nat) : edgeDiffs c.reverse=(edgeDiffs c).reverse := by
  induction c with
  | nil => rfl
  | cons a c ih =>
    cases c with
    | nil => rfl
    | cons b c =>
      rw [List.reverse_cons,edgeDiffs_join _ b a [] (by simp),ih]
      simp [edgeDiffs,distance_comm]

def selectedArm (p : Nat) (c : List Nat) := coreLabels (4*p+6) c ++ [3*p+3,p+1,3*p+4]
def oppositeArm (p : Nat) := oppositePairs p ++ [3*p+6,p,3*p+5]

theorem selected_arm_differences (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    edgeDiffs ((2*p+2)::selectedArm p c) =
      [2*p+1] ++ (edgeSums c).map (fun q => 4*p+6-q) ++ [2*p+7,2*p+2,2*p+3] := by
  have hp := hc.1
  have hb := decoded_core_boundaries p c hc
  obtain ⟨tail,htail⟩ := List.head?_eq_some_iff.mp hb.1
  have hstart : edgeDiffs ((2*p+2)::selectedArm p c) =
      distance (2*p+2) (4*p+3) :: edgeDiffs (selectedArm p c) := by
    simp only [selectedArm,htail,List.cons_append,edgeDiffs]
  rw [hstart]
  unfold selectedArm
  rw [edgeDiffs_join _ (p-4) (3*p+3) [p+1,3*p+4] hb.2]
  rw [coreLabels_decode,decode_core_edge_values p c true (boundary_entries_small p c hc)]
  simp only [edgeDiffs,List.cons_append,List.nil_append]
  have h0 : distance (2*p+2) (4*p+3)=2*p+1 := by unfold distance; omega
  have h1 : distance (p-4) (3*p+3)=2*p+7 := by unfold distance; omega
  have h2 : distance (3*p+3) (p+1)=2*p+2 := by unfold distance; omega
  have h3 : distance (p+1) (3*p+4)=2*p+3 := by unfold distance; omega
  simp [h0,h1,h2,h3]

def pairBlock (p j n : Nat) := (List.range' j n).flatMap (fun i => [2*p+3+i,2*p+1-i])

theorem pair_block_differences (p j n : Nat) (tail : List Nat) (h : j+n ≤ p) :
    edgeDiffs ((2*p+2-j)::(pairBlock p j n ++ tail)) =
      List.range' (2*j+1) (2*n) ++ edgeDiffs ((2*p+2-(j+n))::tail) := by
  induction n generalizing j with
  | zero => simp [pairBlock]
  | succ n ih =>
    have hnext : j+1+n ≤ p := by omega
    have hlow : 2*p+1-j=2*p+2-(j+1) := by omega
    have h1 : distance (2*p+2-j) (2*p+3+j)=2*j+1 := by unfold distance; omega
    have h2 : distance (2*p+3+j) (2*p+1-j)=2*j+2 := by unfold distance; omega
    simp only [pairBlock,List.range'_succ,List.flatMap_cons,List.cons_append,List.nil_append]
    change distance (2*p+2-j) (2*p+3+j) :: distance (2*p+3+j) (2*p+1-j) ::
      edgeDiffs ((2*p+1-j)::(pairBlock p (j+1) n ++ tail)) = _
    rw [h1,h2,hlow,ih (j+1) hnext]
    rw [show 2*(n+1)=2*n+1+1 by omega,List.range'_succ,List.range'_succ]
    simp only [List.cons_append]
    congr 3
    simp [Nat.add_comm,Nat.add_left_comm]

theorem opposite_arm_differences (p : Nat) :
    edgeDiffs ((2*p+2)::oppositeArm p) =
      List.range' 1 (2*p) ++ [2*p+4,2*p+6,2*p+5] := by
  have h := pair_block_differences p 0 p [3*p+6,p,3*p+5] (by omega)
  have hlow : 2*p+2-p=p+2 := by omega
  have h1 : distance (p+2) (3*p+6)=2*p+4 := by unfold distance; omega
  have h2 : distance (3*p+6) p=2*p+6 := by unfold distance; omega
  have h3 : distance p (3*p+5)=2*p+5 := by unfold distance; omega
  simpa [oppositeArm,oppositePairs,pairBlock,List.range_eq_range',hlow,edgeDiffs,h1,h2,h3] using h

theorem full_path_edge_decomposition (p : Nat) (c : List Nat) :
    edgeDiffs (completePath p c)=
      (edgeDiffs ((2*p+2)::selectedArm p c)).reverse ++
      edgeDiffs ((2*p+2)::oppositeArm p) := by
  have hshape : completePath p c=(selectedArm p c).reverse ++ (2*p+2)::oppositeArm p := by
    simp [completePath,selectedArm,oppositeArm,oppositePairs,List.append_assoc]
  rw [hshape,edgeDiffs_overlap]
  have hr : (selectedArm p c).reverse ++ [2*p+2]=((2*p+2)::selectedArm p c).reverse := by simp
  rw [hr,edgeDiffs_reverse]

theorem complete_path_differences (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    (edgeDiffs (completePath p c)).Perm (List.range' 1 (4*p+6)) := by
  rw [full_path_edge_decomposition,selected_arm_differences p c hc,opposite_arm_differences]
  have hrev := (List.reverse_perm
    ([2*p+1] ++ (edgeSums c).map (fun q => 4*p+6-q) ++ [2*p+7,2*p+2,2*p+3])).append
    (List.Perm.refl (List.range' 1 (2*p) ++ [2*p+4,2*p+6,2*p+5]))
  apply hrev.trans
  have hswap : (([2*p+1] ++ (edgeSums c).map (fun q => 4*p+6-q) ++ [2*p+7,2*p+2,2*p+3]) ++
      (List.range' 1 (2*p) ++ [2*p+4,2*p+6,2*p+5])).Perm
      (shellDiffs p ++ (edgeSums c).map (fun q => 4*p+6-q)) := by
    apply List.perm_iff_count.mpr
    intro x
    simp [shellDiffs,List.count_cons]
    omega
  exact hswap.trans (shell_plus_core_differences p (by have hp := hc.1; omega) (edgeSums c) hc.2.2.2.2.1)

def cross (A a b : Nat) : Prop := (a ≤ A ∧ A < b) ∨ (b ≤ A ∧ A < a)

theorem cross_symm (A a b : Nat) (h : cross A a b) : cross A b a := by
  unfold cross at *; omega

theorem crosses_prepend (A a b : Nat) (c : List Nat)
    (hc : crosses A c) (hh : c.head?=some b) (hab : cross A a b) : crosses A (a::c) := by
  obtain ⟨tail,ht⟩ := List.head?_eq_some_iff.mp hh
  rw [ht] at hc ⊢
  exact ⟨hab,hc⟩

theorem crosses_join (A : Nat) (u : List Nat) (a b : Nat) (v : List Nat)
    (hu : crosses A u) (hv : crosses A (b::v)) (hlast : u.getLast?=some a)
    (hab : cross A a b) : crosses A (u++b::v) := by
  induction u with
  | nil => simp at hlast
  | cons x u ih =>
    cases u with
    | nil => simp at hlast; subst x; exact ⟨hab,hv⟩
    | cons y u =>
      have ht : (y::u).getLast?=some a := by simpa using hlast
      exact ⟨hu.1,ih hu.2 ht⟩

theorem crosses_reverse (A : Nat) (c : List Nat) (hc : crosses A c) : crosses A c.reverse := by
  induction c with
  | nil => trivial
  | cons a c ih =>
    cases c with
    | nil => trivial
    | cons b c =>
      rw [List.reverse_cons]
      exact crosses_join A (b::c).reverse b a [] (ih hc.2) trivial (by simp) (cross_symm A a b hc.1)

theorem crosses_overlap (A : Nat) (u : List Nat) (a : Nat) (v : List Nat)
    (hu : crosses A (u++[a])) (hv : crosses A (a::v)) : crosses A (u++a::v) := by
  induction u with
  | nil => exact hv
  | cons b u ih =>
    cases u with
    | nil => exact ⟨hu.1,hv⟩
    | cons d u => exact ⟨hu.1,ih hu.2⟩

theorem decoded_core_crosses (p : Nat) (c : List Nat) (high : Bool)
    (hc : ∀ x ∈ c, x<p) : crosses (2*p+2) (decode (4*p+6) high c) := by
  induction c using edgeSums.induct generalizing high with
  | case1 => trivial
  | case2 a => cases high <;> trivial
  | case3 a b xs ih =>
    have ha := hc a (by simp)
    have hb := hc b (by simp)
    have ht : ∀ x ∈ b::xs, x<p := by intro x hx; exact hc x (by simp [hx])
    cases high with
    | false =>
      change cross (2*p+2) a (4*p+6-b) ∧ crosses (2*p+2) (decode (4*p+6) true (b::xs))
      exact ⟨Or.inl ⟨by omega,by omega⟩,ih true ht⟩
    | true =>
      change cross (2*p+2) (4*p+6-a) b ∧ crosses (2*p+2) (decode (4*p+6) false (b::xs))
      exact ⟨Or.inr ⟨by omega,by omega⟩,ih false ht⟩

theorem selected_arm_crosses (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    crosses (2*p+2) ((2*p+2)::selectedArm p c) := by
  have hp := hc.1
  have hb := decoded_core_boundaries p c hc
  have hcore : crosses (2*p+2) (coreLabels (4*p+6) c) := by
    rw [coreLabels_decode]
    exact decoded_core_crosses p c true (boundary_entries_small p c hc)
  have htail : crosses (2*p+2) [3*p+3,p+1,3*p+4] := by simp [crosses]; omega
  have hab : cross (2*p+2) (p-4) (3*p+3) := Or.inl ⟨by omega,by omega⟩
  have harm := crosses_join (2*p+2) (coreLabels (4*p+6) c) (p-4) (3*p+3) [p+1,3*p+4] hcore htail hb.2 hab
  have hhead : (selectedArm p c).head?=some (4*p+3) := by
    simp [selectedArm,List.head?_append,hb.1]
  exact crosses_prepend (2*p+2) (2*p+2) (4*p+3) (selectedArm p c) harm hhead
    (Or.inl ⟨by omega,by omega⟩)

theorem pair_block_crosses (p j n : Nat) (tail : List Nat) (h : j+n ≤ p)
    (htail : crosses (2*p+2) ((2*p+2-(j+n))::tail)) :
    crosses (2*p+2) ((2*p+2-j)::(pairBlock p j n ++ tail)) := by
  induction n generalizing j with
  | zero => simpa [pairBlock] using htail
  | succ n ih =>
    have hnext : j+1+n ≤ p := by omega
    have hlow : 2*p+1-j=2*p+2-(j+1) := by omega
    have htail' : crosses (2*p+2) ((2*p+2-(j+1+n))::tail) := by
      simpa [Nat.add_comm,Nat.add_left_comm] using htail
    have hi := ih (j+1) hnext htail'
    simp only [pairBlock,List.range'_succ,List.flatMap_cons,List.cons_append,List.nil_append]
    change cross (2*p+2) (2*p+2-j) (2*p+3+j) ∧
      cross (2*p+2) (2*p+3+j) (2*p+1-j) ∧
      crosses (2*p+2) ((2*p+1-j)::(pairBlock p (j+1) n ++ tail))
    refine ⟨Or.inl ⟨by omega,by omega⟩,Or.inr ⟨by omega,by omega⟩,?_⟩
    rw [hlow]
    exact hi

theorem opposite_arm_crosses (p : Nat) : crosses (2*p+2) ((2*p+2)::oppositeArm p) := by
  have ht : crosses (2*p+2) ((2*p+2-(0+p))::[3*p+6,p,3*p+5]) := by
    simp [crosses]; omega
  have h := pair_block_crosses p 0 p [3*p+6,p,3*p+5] (by omega) ht
  simpa [oppositeArm,oppositePairs,pairBlock,List.range_eq_range'] using h

theorem complete_path_crosses (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    crosses (2*p+2) (completePath p c) := by
  have hleft := crosses_reverse (2*p+2) ((2*p+2)::selectedArm p c) (selected_arm_crosses p c hc)
  have hright := opposite_arm_crosses p
  have hshape : completePath p c=(selectedArm p c).reverse ++ (2*p+2)::oppositeArm p := by
    simp [completePath,selectedArm,oppositeArm,oppositePairs,List.append_assoc]
  rw [hshape]
  exact crosses_overlap (2*p+2) (selectedArm p c).reverse (2*p+2) (oppositeArm p)
    (by simpa using hleft) hright

theorem selected_arm_length (p : Nat) (c : List Nat) (hlen : c.length=2*p) :
    (selectedArm p c).length=2*p+3 := by simp [selectedArm,coreLabels,hlen]

theorem complete_path_midpoint (p : Nat) (c : List Nat) (hc : BoundaryCore p c) :
    (completePath p c)[2*p+3]?=some (2*p+2) := by
  have hlen := selected_arm_length p c hc.2.1
  have hshape : completePath p c=(selectedArm p c).reverse ++ (2*p+2)::oppositeArm p := by
    simp [completePath,selectedArm,oppositeArm,oppositePairs,List.append_assoc]
  rw [hshape,List.getElem?_append_right (by simp [hlen])]
  simp [hlen]

/-- Every given offset-3 balanced core admits the actual midpoint alpha shell. -/
theorem boundary_shell_bridge : BoundaryShellBridge := by
  intro p c hc
  have hv := complete_path_labels p c hc
  refine ⟨?_,hv,complete_path_differences p c hc,complete_path_crosses p c hc,
    complete_path_midpoint p c hc⟩
  simpa using hv.length_eq

theorem complete_path_core_lookup (p : Nat) (c : List Nat) (i : Nat)
    (hlen : c.length=2*p) (hi : i < 2*p) :
    (completePath p c)[2*p+2-i]?=(coreLabels (4*p+6) c)[i]? := by
  have ha := selected_arm_length p c hlen
  have hshape : completePath p c=(selectedArm p c).reverse ++ (2*p+2)::oppositeArm p := by
    simp [completePath,selectedArm,oppositeArm,oppositePairs,List.append_assoc]
  rw [hshape,List.getElem?_append_left (by simp [ha]; omega)]
  have hr : ((selectedArm p c).reverse)[2*p+2-i]?=(selectedArm p c)[i]? :=
    List.getElem?_reverse' (by rw [ha]; omega)
  rw [hr]
  unfold selectedArm
  rw [List.getElem?_append_left (by rw [coreLabels_length,hlen]; exact hi)]

/-- The arbitrary anchored core produces the specified simultaneous zero and
    maximum positions on its chosen arm. -/
theorem core_to_path_bridge : CoreToPathBridge := by
  intro s c hc
  have hs := hc.1
  have hboundary := core_boundary_contract s c hc
  have hgeneric := boundary_shell_bridge (3*s) c hboundary
  have hlen : c.length=2*(3*s) := by simpa [show 2*(3*s)=6*s by omega] using hc.2.1
  have hzero := hc.2.2.2.2.2.2.2.2.1
  have hmax := hc.2.2.2.2.2.2.2.2.2.1
  have hz := complete_path_core_lookup (3*s) c (4*s-1) hlen (by omega)
  have hm := complete_path_core_lookup (3*s) c (4*s) hlen (by omega)
  rw [coreLabels_lookup,hzero] at hz
  rw [coreLabels_lookup,hmax] at hm
  have e1 : 2*(3*s)+2-(4*s-1)=2*s+3 := by omega
  have e2 : 2*(3*s)+2-4*s=2*s+2 := by omega
  have hodd : ¬ (4*s-1)%2=0 := by omega
  have heven : (4*s)%2=0 := by omega
  simp only [e1,hodd,ite_false,Option.map_some] at hz
  simp only [e2,heven,ite_true,Option.map_some,Nat.sub_zero] at hm
  rcases hgeneric with ⟨hl,hv,he,ha,hmid⟩
  have h12 : 4*(3*s)=12*s := by omega
  have h6 : 2*(3*s)=6*s := by omega
  exact ⟨by simpa only [h12] using hl,by simpa only [h12] using hv,
    by simpa only [h12] using he,by simpa only [h6] using ha,
    by simpa only [h6] using hmid,hz,by simpa only [h12] using hm⟩

/-- Unconditional all-s existence of the complete midpoint alpha-path
    certificates, including the adjacent prescribed-depth extreme labels. -/
theorem uniform_midpoint_alpha_paths :
    ∀ s, 2 ≤ s → ∃ path, PathCertificate s path := by
  intro s hs
  obtain ⟨c,hc⟩ := uniform_anchored_cores s hs
  exact ⟨completePath (3*s) c,core_to_path_bridge s c hc⟩
end GracefulBoundary







