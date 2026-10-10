import Zigzag
namespace GracefulBoundary.EvenUniform

theorem reflected_interval (N lo n : Nat) (h : lo+n≤N+1) :
    ((List.range' lo n).map (fun x => N-x)).Perm (List.range' (N+1-lo-n) n) := by
  by_cases empty : n=0
  · subst n; simp
  · have he : (List.range' (N+1-lo-n) n).reverse=(List.range' lo n).map (fun x => N-x) := by
      rw [List.reverse_range',List.range'_eq_map_range,List.map_map]
      have top : N+1-lo-n+n-1=N-lo := by omega
      rw [top]
      apply List.map_congr_left
      intro i _
      dsimp only [Function.comp_apply]
      omega
    rw [←he]; exact List.reverse_perm _

theorem auxiliary_entries (r : Nat) (c : List Nat) (hc : Auxiliary r c) : ∀x∈c,x≤r := by
  intro x hx
  have hp := List.count_pos_iff.mpr hx
  have hsum := count_sides x c
  have hlo := hc.low.count_eq x
  have hhi := hc.high.count_eq x
  simp only [List.count_cons,count_band,List.count_range,Nat.beq_eq_true_eq] at hlo hhi
  repeat (any_goals (first | omega | split at *))

theorem decoded_auxiliary_labels (r : Nat) (c : List Nat) (hc : Auxiliary r c) :
    (decode (4*r-2) false c).Perm ((0::List.range' 2 (r-1))++List.range' (3*r) (r-1)) := by
  have hr := hc.lower
  have high := hc.high.map (fun x => 4*r-2-x)
  have reflected := reflected_interval (4*r-2) 0 (r-1) (by omega)
  simp only [←List.range_eq_range',show 4*r-2+1-0-(r-1)=3*r by omega] at reflected
  exact (decode_side_permutations (4*r-2) c).2.trans (hc.low.append (high.trans reflected))

theorem decoded_auxiliary_differences (r : Nat) (c : List Nat) (hc : Auxiliary r c) :
    (edgeDiffs (decode (4*r-2) false c)).Perm (List.range' (2*r) (2*r-2)) := by
  have hr := hc.lower
  have bounds : ∀s∈edgeSums c,s≤4*r-2 := by
    intro s hs
    have h := hc.sums.mem_iff.mp hs
    obtain ⟨i,hi,he⟩ := List.mem_range'.mp h
    omega
  rw [LabelOne.decode_sums _ c false bounds]
  have hp := hc.sums.map (fun x => 4*r-2-x)
  have reflected := reflected_interval (4*r-2) 1 (2*r-2) (by omega)
  have lo : 4*r-2+1-1-(2*r-2)=2*r := by omega
  rw [lo] at reflected
  exact hp.trans reflected

theorem decoded_small_crosses (N A bound : Nat) (c : List Nat) (b : Bool)
    (hsmall : ∀x∈c,x≤bound) (hlo : bound≤A) (hhi : A<N-bound) : crosses A (decode N b c) := by
  induction c using edgeSums.induct generalizing b with
  | case1 => trivial
  | case2 a => cases b <;> trivial
  | case3 a x c ih =>
    have ha := hsmall a (by simp)
    have hx := hsmall x (by simp)
    have ht : ∀y∈x::c,y≤bound := by intro y hy; exact hsmall y (by simp [hy])
    cases b with
    | false => change cross A a (N-x) ∧ crosses A (decode N true (x::c)); exact ⟨Or.inl ⟨by omega,by omega⟩,ih true ht⟩
    | true => change cross A (N-a) x ∧ crosses A (decode N false (x::c)); exact ⟨Or.inr ⟨by omega,by omega⟩,ih false ht⟩

theorem decoded_auxiliary_crosses (r : Nat) (c : List Nat) (hc : Auxiliary r c) :
    crosses (2*r) (decode (4*r-2) false c) :=
  decoded_small_crosses (4*r-2) (2*r) r c false (auxiliary_entries r c hc) (by omega) (by have := hc.lower; omega)

theorem crosses_translate (A t : Nat) (c : List Nat) (hc : crosses A c) : crosses (t+A) (c.map (fun x => t+x)) := by
  induction c using crosses.induct with
  | case1 => trivial
  | case2 a => trivial
  | case3 a b c ih =>
    change cross (t+A) (t+a) (t+b) ∧ crosses (t+A) ((b::c).map (fun x => t+x))
    refine ⟨?_,ih hc.2⟩
    have hab : cross A a b := hc.1
    dsimp only [cross] at hab ⊢
    omega

def alphaPrefix (r : Nat) := (zigList (2*r-2)).map (fun x => r+1+x)
def alphaPath (r : Nat) (c : List Nat) := alphaPrefix r++[4*r-1,1,4*r]++decode (4*r-2) false c

theorem prefix_labels (r : Nat) : (alphaPrefix r).Perm (List.range' (r+1) (2*r-2+1)) := by
  have hp := (zig_labels (2*r-2)).map (fun x => r+1+x)
  rw [←List.range'_eq_map_range] at hp
  exact hp

theorem prefix_last (r : Nat) (hr : 3≤r) : (alphaPrefix r).getLast?=some (2*r) := by
  rw [alphaPrefix,List.getLast?_map,zig_last]
  simp only [Option.map_some]
  congr 1
  dsimp only [zig]
  rw [ite_eq_left (by omega)]
  omega

theorem prefix_crosses (r : Nat) (hr : 3≤r) : crosses (2*r) (alphaPrefix r) := by
  have hc := crosses_translate ((2*r-2)/2) (r+1) (zigList (2*r-2)) (zig_crosses (2*r-2))
  have eq : r+1+(2*r-2)/2=2*r := by omega
  rw [eq] at hc; exact hc

theorem alpha_path_certificate (r : Nat) (c : List Nat) (hc : Auxiliary r c) :
    (alphaPath r c).length=4*r+1 ∧ (alphaPath r c).Perm (List.range (4*r+1)) ∧
    (edgeDiffs (alphaPath r c)).Perm (List.range' 1 (4*r)) ∧ crosses (2*r) (alphaPath r c) ∧
    (alphaPath r c)[2*r]?=some 1 ∧ (alphaPath r c)[2*r+1]?=some (4*r) ∧ (alphaPath r c)[2*r+2]?=some 0 := by
  have hr := hc.lower
  have prefixLen : (alphaPrefix r).length=2*r-1 := by simp [alphaPrefix,zigList]; omega
  obtain ⟨tail,ct⟩ := List.head?_eq_some_iff.mp hc.first
  have decoded : decode (4*r-2) false c=0::decode (4*r-2) true tail := by rw [ct]; rfl
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [alphaPath,List.length_append,prefixLen,List.length_cons,List.length_nil,LabelOne.decode_length,hc.length]; omega
  · have hp := ((prefix_labels r).append (List.Perm.refl [4*r-1,1,4*r])).append (decoded_auxiliary_labels r c hc)
    apply hp.trans
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,count_band,Nat.beq_eq_true_eq]
    repeat (any_goals (first | omega | split))
  · have shape : edgeDiffs (alphaPath r c)=edgeDiffs (alphaPrefix r)++[2*r-1,4*r-2,4*r-1,4*r]++edgeDiffs (decode (4*r-2) false c) := by
      dsimp only [alphaPath]
      rw [List.append_assoc]
      change edgeDiffs (alphaPrefix r++(4*r-1)::([1,4*r]++decode (4*r-2) false c))=_
      rw [edgeDiffs_join _ (2*r) _ _ (prefix_last r hr),decoded]
      simp only [List.cons_append,List.nil_append,edgeDiffs,distance]
      have a : 2*r-(4*r-1)+(4*r-1-2*r)=2*r-1 := by omega
      have b : 4*r-1-1+(1-(4*r-1))=4*r-2 := by omega
      have d : 1-4*r+(4*r-1)=4*r-1 := by omega
      simp only [a,b,d,Nat.sub_zero,Nat.zero_sub,Nat.add_zero,List.append_assoc,List.cons_append,List.nil_append]
    rw [shape]
    have pp : (edgeDiffs (alphaPrefix r)).Perm (List.range' 1 (2*r-2)) := by
      rw [alphaPrefix,LabelOne.translated_edges]
      exact zig_differences (2*r-2)
    have hp := (pp.append (List.Perm.refl [2*r-1,4*r-2,4*r-1,4*r])).append (decoded_auxiliary_differences r c hc)
    apply hp.trans
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.count_append,List.count_cons,List.count_nil,count_band,Nat.beq_eq_true_eq]
    repeat (any_goals (first | omega | split))
  · have ht := decoded_auxiliary_crosses r c hc
    rw [decoded] at ht
    have block : crosses (2*r) ([4*r-1,1,4*r]++decode (4*r-2) false c) := by
      rw [decoded]
      change cross (2*r) (4*r-1) 1 ∧ cross (2*r) 1 (4*r) ∧ cross (2*r) (4*r) 0 ∧ crosses (2*r) (0::decode (4*r-2) true tail)
      refine ⟨Or.inr ⟨by omega,by omega⟩,Or.inl ⟨by omega,by omega⟩,Or.inr ⟨by omega,by omega⟩,ht⟩
    have joined := crosses_join (2*r) (alphaPrefix r) (2*r) (4*r-1) ([1,4*r]++decode (4*r-2) false c) (prefix_crosses r hr) block (prefix_last r hr) (Or.inl ⟨by omega,by omega⟩)
    simpa only [alphaPath,List.append_assoc,List.cons_append,List.nil_append] using joined
  · simp only [alphaPath,List.append_assoc]
    rw [List.getElem?_append_right (by rw [prefixLen]; omega),prefixLen,show 2*r-(2*r-1)=1 by omega]
    rfl
  · simp only [alphaPath,List.append_assoc]
    rw [List.getElem?_append_right (by rw [prefixLen]; omega),prefixLen,show 2*r+1-(2*r-1)=2 by omega]
    rfl
  · simp only [alphaPath,List.append_assoc]
    rw [List.getElem?_append_right (by rw [prefixLen]; omega),prefixLen,show 2*r+2-(2*r-1)=3 by omega]
    rw [decoded]
    rfl

theorem all_anchored_alpha_paths (r : Nat) (hr : 3≤r) :
    ∃ f : Fin (2*(2*r)+1) → Nat, Graceful (pathGraph (2*(2*r))) (2*(2*r)) f ∧ Alpha (pathGraph (2*(2*r))) (2*r) f ∧
      f ⟨2*r,by omega⟩=1 ∧ f ⟨2*r+1,by omega⟩=2*(2*r) ∧ f ⟨2*r+2,by omega⟩=0 := by
  obtain ⟨c,hc⟩ := auxiliaries r hr
  obtain ⟨len,hv,he,ha,h1,hmax,hzero⟩ := alpha_path_certificate r c hc
  have size : 4*r=2*(2*r) := by omega
  rw [size] at len hv he hmax
  refine ⟨pathLabel (2*(2*r)) (alphaPath r c),list_path_graceful (2*(2*r)) _ hv he,list_path_alpha (2*(2*r)) (2*r) _ len ha,?_,?_,?_⟩
  · simp [pathLabel,List.getD_eq_getElem?_getD,h1]
  · simp [pathLabel,List.getD_eq_getElem?_getD,hmax]
  · simp [pathLabel,List.getD_eq_getElem?_getD,hzero]

end GracefulBoundary.EvenUniform
