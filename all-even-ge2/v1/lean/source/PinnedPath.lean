import BandInsertion
namespace GracefulBoundary.CenterLeaves
open LabelOne

theorem prefix_reverse_lookup (k i : Nat) (hi : i<k+3) :
    (waleckiPrefix k).reverse[k+2-i]?=some (walecki k i) := by
  have len : (waleckiPrefix k).length=k+3 := by simp [waleckiPrefix]
  rw [List.getElem?_reverse' (i:=k+2-i) (j:=i) (by rw [len]; omega)]
  simp only [waleckiPrefix,List.getElem?_map,List.getElem?_range hi,Option.map_some]

theorem residual_pins (k : Nat) (tail : List Nat) (hk : 7≤k) :
    (residualPath k tail)[k]?=some 1 ∧
    (residualPath k tail)[k+1]?=some (2*k) ∧ (residualPath k tail)[k+2]?=some 0 := by
  have len : (waleckiPrefix k).reverse.length=k+3 := by simp [waleckiPrefix]
  have at2 := prefix_reverse_lookup k 2 (by omega)
  have at1 := prefix_reverse_lookup k 1 (by omega)
  have at0 := prefix_reverse_lookup k 0 (by omega)
  have hk2 : k+2-2=k := by omega
  have hk1 : k+2-1=k+1 := by omega
  have hk0 : k+2-0=k+2 := by omega
  simp only [hk2,hk1,hk0,walecki] at at2 at1 at0
  constructor
  · rw [residualPath,List.getElem?_append_left (by omega)]; exact at2
  constructor
  · rw [residualPath,List.getElem?_append_left (by omega)]; exact at1
  · rw [residualPath,List.getElem?_append_left (by omega)]; exact at0

theorem anchored_residual_path (k : Nat) (hk : 7≤k) :
    ∃ c,c.length=2*k+1 ∧ c.Perm (List.range (2*k+1)) ∧
      (edgeDiffs c).Perm (List.range' 1 (2*k)) ∧ c[k]?=some 1 ∧ c[k+1]?=some (2*k) ∧ c[k+2]?=some 0 := by
  obtain ⟨tail,len,labels,edges,first⟩ := anchored_permutations (k-2) (by omega)
  have tailLabels := labels.map (fun x => k/2+2+x)
  rw [←List.range'_eq_map_range] at tailLabels
  have lp := prefix_labels k hk
  have prefixLen : (waleckiPrefix k).length=k+3 := by simp [waleckiPrefix]
  have root : (waleckiPrefix k).head?=some 0 := by simp [waleckiPrefix,List.head?_eq_getElem?,walecki]
  have last : (waleckiPrefix k).reverse.getLast?=some 0 := by simpa only [List.getLast?_reverse] using root
  have start : (tail.map (fun x => k/2+2+x)).head?=some (k-2) := by
    rw [List.head?_map,first]
    simp only [Option.map_some]
    congr 1
    omega
  refine ⟨residualPath k tail,by simp [residualPath,prefixLen,len]; omega,?_,?_,?_⟩
  · have perm := ((List.reverse_perm _).trans lp).append tailLabels
    apply perm.trans
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.count_append,List.count_range,count_band]
    repeat (any_goals (first | omega | split))
  · have shape : edgeDiffs (residualPath k tail)=
      edgeDiffs (waleckiPrefix k).reverse++(k-2)::edgeDiffs (tail.map (fun x => k/2+2+x)) := by
      obtain ⟨ts,he⟩ := List.head?_eq_some_iff.mp start
      dsimp only [residualPath]
      rw [he,edgeDiffs_join _ 0 (k-2) ts last]
      simp only [distance,Nat.zero_sub,Nat.sub_zero,Nat.zero_add]
    rw [shape,translated_edges]
    have perm := (prefix_differences k hk).append (edges.cons (k-2))
    apply perm.trans
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.count_append,List.count_cons,count_band,Nat.beq_eq_true_eq]
    repeat (any_goals (first | omega | split))
  · exact residual_pins k tail hk

theorem midpoint_pinned_graceful_path (k : Nat) (hk : 7≤k) :
    ∃ f : Fin (2*k+1) → Nat, Graceful (pathGraph (2*k)) (2*k) f ∧
      f ⟨k,by omega⟩=1 ∧ f ⟨k+1,by omega⟩=2*k ∧ f ⟨k+2,by omega⟩=0 := by
  obtain ⟨c,_,hv,he,hm,hmax,hzero⟩ := anchored_residual_path k hk
  refine ⟨pathLabel (2*k) c,list_path_graceful (2*k) c hv he,?_,?_,?_⟩
  · simp [pathLabel,List.getD_eq_getElem?_getD,hm]
  · simp [pathLabel,List.getD_eq_getElem?_getD,hmax]
  · simp [pathLabel,List.getD_eq_getElem?_getD,hzero]

end GracefulBoundary.CenterLeaves

