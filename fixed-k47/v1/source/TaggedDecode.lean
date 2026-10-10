import K23Packets
namespace GracefulBoundary.WholeTagged

theorem tagged_entries_bound (k : Nat) (c : List Nat)
    (hh : (highs c).Perm (List.range (k+1)))
    (hl : (lows c).Perm (List.range k)) : ∀ x ∈ c, x≤k := by
  intro x hx
  have hc := count_sides x c
  have hz := List.count_pos_iff.mpr hx
  have hhigh := hh.count_eq x
  have hlow := hl.count_eq x
  simp only [List.count_range] at hhigh hlow
  by_cases hb : x≤k
  · exact hb
  · have hn : ¬x<k+1 := by omega
    have hn' : ¬x<k := by omega
    simp only [hn,hn',ite_false] at hhigh hlow
    omega

theorem tagged_high_bound (k : Nat) (c : List Nat)
    (hh : (highs c).Perm (List.range (k+1))) : ∀ x ∈ highs c, x≤k := by
  intro x hx
  have hmem := hh.mem_iff.mp hx
  have hb := List.mem_range.mp hmem
  omega

theorem tagged_low_bound (k : Nat) (c : List Nat)
    (hl : (lows c).Perm (List.range k)) : ∀ x ∈ lows c, x<k := by
  intro x hx
  exact List.mem_range.mp (hl.mem_iff.mp hx)

theorem tagged_labels (k : Nat) (c : List Nat)
    (hh : (highs c).Perm (List.range (k+1)))
    (hl : (lows c).Perm (List.range k)) :
    (coreLabels (2*k) c).Perm (List.range (2*k+1)) := by
  have reflected : ((List.range (k+1)).map (fun x => 2*k-x)).Perm (List.range' k (k+1)) := by
    have he : (List.range' k (k+1)).reverse=(List.range (k+1)).map (fun x => 2*k-x) := by
      rw [List.reverse_range',show k+(k+1)-1=2*k by omega]
    rw [← he]
    exact List.reverse_perm _
  have bands : (List.range' k (k+1) ++ List.range k).Perm (List.range (2*k+1)) := by
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.count_append,count_band,List.count_range]
    repeat (any_goals split)
    all_goals omega
  rw [coreLabels_decode]
  exact (decode_side_permutations (2*k) c).1.trans
    ((((hh.map (fun x => 2*k-x)).trans reflected).append hl).trans bands)

theorem tagged_edge_values (k : Nat) (c : List Nat) (high : Bool)
    (hc : ∀ x ∈ c,x≤k) :
    edgeDiffs (decode (2*k) high c)=(edgeSums c).map (fun s => 2*k-s) := by
  induction c using edgeSums.induct generalizing high with
  | case1 => rfl
  | case2 a => cases high <;> rfl
  | case3 a b xs ih =>
    have ha := hc a (by simp)
    have hb := hc b (by simp)
    have ht : ∀ x ∈ b::xs,x≤k := by intro x hx; exact hc x (by simp [hx])
    cases high with
    | false =>
      change distance a (2*k-b) :: edgeDiffs (decode (2*k) true (b::xs)) = _
      rw [ih true ht]
      simp only [edgeSums,List.map_cons]
      congr 1
      simp only [distance]
      omega
    | true =>
      change distance (2*k-a) b :: edgeDiffs (decode (2*k) false (b::xs)) = _
      rw [ih false ht]
      simp only [edgeSums,List.map_cons]
      congr 1
      simp only [distance]
      omega

theorem tagged_edges (k : Nat) (c : List Nat)
    (hh : (highs c).Perm (List.range (k+1)))
    (hl : (lows c).Perm (List.range k))
    (he : (edgeSums c).Perm (List.range (2*k))) :
    (edgeDiffs (coreLabels (2*k) c)).Perm (List.range' 1 (2*k)) := by
  rw [coreLabels_decode,tagged_edge_values k c true (tagged_entries_bound k c hh hl)]
  have hm := he.map (fun s => 2*k-s)
  have hr : (List.range' 1 (2*k)).reverse=(List.range (2*k)).map (fun s => 2*k-s) := by
    rw [List.reverse_range']
    simp
  rw [← hr] at hm
  exact hm.trans (List.reverse_perm _)

theorem tagged_crosses_aux (k : Nat) (hk : 1≤k) (c : List Nat) (high : Bool)
    (hh : ∀ x ∈ highs c, if high then x≤k else x<k)
    (hl : ∀ x ∈ lows c, if high then x<k else x≤k) :
    crosses (k-1) (decode (2*k) high c) := by
  induction c using edgeSums.induct generalizing high with
  | case1 => trivial
  | case2 a => cases high <;> trivial
  | case3 a b xs ih =>
    have ha := hh a (by simp)
    have hb := hl b (by simp)
    have htH : ∀ x ∈ highs (b::xs), if (!high) then x≤k else x<k := by
      intro x hx
      have h := hl x (by simpa only [lows_cons] using hx)
      cases high <;> simpa using h
    have htL : ∀ x ∈ lows (b::xs), if (!high) then x<k else x≤k := by
      intro x hx
      have h := hh x (by simp only [highs_cons]; exact List.mem_cons_of_mem a hx)
      cases high <;> simpa using h
    cases high with
    | false =>
      simp only [Bool.false_eq_true,ite_false] at ha hb
      change cross (k-1) a (2*k-b) ∧ crosses (k-1) (decode (2*k) true (b::xs))
      exact ⟨Or.inl ⟨by omega,by omega⟩,ih true htH htL⟩
    | true =>
      simp only [ite_true] at ha hb
      change cross (k-1) (2*k-a) b ∧ crosses (k-1) (decode (2*k) false (b::xs))
      exact ⟨Or.inr ⟨by omega,by omega⟩,ih false htH htL⟩

theorem tagged_crosses (k : Nat) (hk : 1≤k) (c : List Nat)
    (hh : (highs c).Perm (List.range (k+1)))
    (hl : (lows c).Perm (List.range k)) :
    crosses (k-1) (coreLabels (2*k) c) := by
  rw [coreLabels_decode]
  exact tagged_crosses_aux k hk c true (tagged_high_bound k c hh) (tagged_low_bound k c hl)

theorem whole_path_certificate (p : Nat) (c : List Nat)
    (hlen : c.length=2*(2*p+3)+1)
    (hh : (highs c).Perm (List.range (2*p+4)))
    (hl : (lows c).Perm (List.range (2*p+3)))
    (he : (edgeSums c).Perm (List.range (4*p+6)))
    (hmid : c[2*p+3]?=some (2*p+2)) :
    GenericPathCertificate p (coreLabels (4*p+6) c) := by
  have hsize : 2*(2*p+3)=4*p+6 := by omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [coreLabels_length,hlen]; omega
  · simpa only [hsize] using tagged_labels (2*p+3) c hh hl
  · simpa only [hsize] using tagged_edges (2*p+3) c hh hl (by simpa only [hsize] using he)
  · simpa only [hsize,show 2*p+3-1=2*p+2 by omega] using tagged_crosses (2*p+3) (by omega) c hh hl
  · rw [coreLabels_lookup,hmid]
    simp only [show ¬(2*p+3)%2=0 by omega,ite_false,Option.map_some]

end GracefulBoundary.WholeTagged
