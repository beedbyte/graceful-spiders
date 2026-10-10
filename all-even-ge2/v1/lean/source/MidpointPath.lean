import Twizzler

namespace GracefulBoundary.LabelOne

def walecki (k i : Nat) : Nat := if i%2=0 then i/2 else 2*k-i/2
def waleckiPrefix (k : Nat) : List Nat := (List.range (k+3)).map (walecki k)
def pairs (k n : Nat) : List Nat := (List.range n).flatMap (fun j => [j,2*k-j])

theorem pair_map (k j n : Nat) :
    (List.range' (2*j) (2*n)).map (walecki k)=
      (List.range' j n).flatMap (fun i => [i,2*k-i]) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,List.range'_succ,List.range'_succ]
    simp only [List.map_cons]
    have half0 : walecki k (2*j)=j := by dsimp only [walecki]; rw [ite_eq_left (by omega)]; omega
    have half1 : walecki k (2*j+1)=2*k-j := by dsimp only [walecki]; rw [ite_eq_right (by omega)]; congr 1 <;> omega
    rw [half0,half1,show 2*j+1+1=2*(j+1) by omega,ih]
    simp only [List.range'_succ,List.flatMap_cons,List.cons_append,List.nil_append]

theorem reflected_initial (k n : Nat) (hn : 1≤n ∧ n≤2*k) :
    ((List.range n).map (fun i => 2*k-i)).Perm (List.range' (2*k-n+1) n) := by
  have he : (List.range' (2*k-n+1) n).reverse=(List.range n).map (fun i => 2*k-i) := by
    rw [List.reverse_range',show 2*k-n+1+n-1=2*k by omega]
  rw [←he]
  exact List.reverse_perm _

theorem pair_labels (k n : Nat) (hn : 1≤n ∧ n≤2*k) :
    (pairs k n).Perm (List.range n++List.range' (2*k-n+1) n) := by
  have hp := pairs_perm (List.range n) id (fun i => 2*k-i)
  simp only [List.map_id] at hp
  exact hp.trans ((List.Perm.refl _).append (reflected_initial k n hn))

theorem prefix_labels (k : Nat) (hk : 7≤k) :
    (waleckiPrefix k).Perm (List.range (k/2+2)++List.range' (k+k/2) (k-k/2+1)) := by
  let n := (k+3)/2
  have base : (List.range (2*n)).map (walecki k)=pairs k n := by
    simpa only [List.range_eq_range',Nat.mul_zero,pairs] using pair_map k 0 n
  have bands := pair_labels k n (by dsimp only [n]; omega)
  by_cases even : k%2=0
  · have shape : waleckiPrefix k=pairs k n++[n] := by
      dsimp only [waleckiPrefix]
      rw [show k+3=2*n+1 by dsimp only [n]; omega,List.range_succ,List.map_append,base]
      have half : walecki k (2*n)=n := by dsimp only [walecki]; rw [ite_eq_left (by omega)]; omega
      simp only [List.map_cons,List.map_nil,half]
    rw [shape]
    apply List.perm_iff_count.mpr
    intro x
    rw [List.count_append,bands.count_eq x]
    simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,count_band,Nat.beq_eq_true_eq]
    dsimp only [n]
    repeat (any_goals (first | omega | split))
  · have shape : waleckiPrefix k=pairs k n := by
      dsimp only [waleckiPrefix]
      rw [show k+3=2*n by dsimp only [n]; omega,base]
    rw [shape]
    have first : n=k/2+2 := by dsimp only [n]; omega
    have lower : 2*k-n+1=k+k/2 := by dsimp only [n]; omega
    have size : n=k-k/2+1 := by dsimp only [n]; omega
    rw [lower,first] at bands
    rw [←size,first]
    exact bands

theorem walecki_edge (k i : Nat) (hi : i<2*k) : distance (walecki k i) (walecki k (i+1))=2*k-i := by
  dsimp only [walecki,distance]
  repeat (any_goals (first | omega | split))

theorem mapped_prefix_edges (k j n : Nat) (hn : j+n≤2*k) :
    edgeDiffs ((List.range' j (n+1)).map (walecki k))=
      (List.range' j n).map (fun i => 2*k-i) := by
  induction n generalizing j with
  | zero => simp [List.range',edgeDiffs]
  | succ n ih =>
    rw [List.range'_succ]
    simp only [List.map_cons]
    have shape : edgeDiffs (walecki k j::(List.range' (j+1) (n+1)).map (walecki k)) =
      distance (walecki k j) (walecki k (j+1))::
        edgeDiffs ((List.range' (j+1) (n+1)).map (walecki k)) := by
      rw [List.range'_succ]
      simp only [List.map_cons,edgeDiffs]
    rw [shape,walecki_edge k j (by omega),ih (j+1) (by omega)]
    simp only [List.range'_succ,List.map_cons]

theorem prefix_differences (k : Nat) (hk : 7≤k) :
    (edgeDiffs (waleckiPrefix k).reverse).Perm (List.range' (k-1) (k+2)) := by
  rw [edgeDiffs_reverse]
  have hp : edgeDiffs (waleckiPrefix k)=(List.range (k+2)).map (fun i => 2*k-i) := by
    simpa only [waleckiPrefix,List.range_eq_range',Nat.zero_add,show k+2+1=k+3 by omega] using
      mapped_prefix_edges k 0 (k+2) (by omega)
  rw [hp]
  have reflected := reflected_initial k (k+2) (by omega)
  have lower : 2*k-(k+2)+1=k-1 := by omega
  rw [lower] at reflected
  exact (List.reverse_perm _).trans reflected

def residualPath (k : Nat) (c : List Nat) : List Nat := (waleckiPrefix k).reverse++c.map (fun x => k/2+2+x)

theorem residual_path (k : Nat) (hk : 7≤k) :
    ∃ c,c.length=2*k+1 ∧ c.Perm (List.range (2*k+1)) ∧
      (edgeDiffs c).Perm (List.range' 1 (2*k)) ∧ c[k]?=some 1 := by
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
  · have source : (waleckiPrefix k)[2]?=some 1 := by simp [waleckiPrefix,walecki]
    have reflected : (waleckiPrefix k).reverse[k]?=(waleckiPrefix k)[2]? := by
      have hr := List.getElem?_reverse' (l:=waleckiPrefix k) (i:=k) (j:=2) (by omega)
      exact hr
    rw [residualPath,List.getElem?_append_left (by rw [List.length_reverse,prefixLen]; omega),reflected,source]

theorem midpoint_one_graceful_path (k : Nat) (hk : 7≤k) :
    ∃ f : Fin (2*k+1) → Nat,Graceful (pathGraph (2*k)) (2*k) f ∧ f ⟨k,by omega⟩=1 := by
  obtain ⟨c,_,hv,he,hm⟩ := residual_path k hk
  exact ⟨pathLabel (2*k) c,list_path_graceful (2*k) c hv he,
    by simp [pathLabel,List.getD_eq_getElem?_getD,hm]⟩

end GracefulBoundary.LabelOne
