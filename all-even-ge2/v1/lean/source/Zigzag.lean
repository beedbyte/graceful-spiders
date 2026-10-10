import AuxiliaryAlpha
namespace GracefulBoundary.EvenUniform

def zig (N i : Nat) := if i%2=0 then i/2 else N-i/2
def zigList (N : Nat) := (List.range (N+1)).map (zig N)

theorem zig_pair_map (N j n : Nat) :
    (List.range' (2*j) (2*n)).map (zig N)=(List.range' j n).flatMap (fun i => [i,N-i]) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,List.range'_succ,List.range'_succ]
    simp only [List.map_cons]
    have h0 : zig N (2*j)=j := by dsimp only [zig]; rw [ite_eq_left (by omega)]; omega
    have h1 : zig N (2*j+1)=N-j := by dsimp only [zig]; rw [ite_eq_right (by omega)]; congr 1 <;> omega
    rw [h0,h1,show 2*j+1+1=2*(j+1) by omega,ih]
    simp only [List.range'_succ,List.flatMap_cons,List.cons_append,List.nil_append]

theorem descending_band (N n : Nat) (hn : 1≤n ∧ n≤N) :
    ((List.range n).map (fun i => N-i)).Perm (List.range' (N-n+1) n) := by
  have he : (List.range' (N-n+1) n).reverse=(List.range n).map (fun i => N-i) := by
    rw [List.reverse_range',show N-n+1+n-1=N by omega]
  rw [←he]; exact List.reverse_perm _

theorem zig_labels (N : Nat) : (zigList N).Perm (List.range (N+1)) := by
  by_cases zero : N=0
  · subst N; decide
  let n := (N+1)/2
  have base : (List.range (2*n)).map (zig N)=(List.range n).flatMap (fun i => [i,N-i]) := by
    simpa only [List.range_eq_range',Nat.mul_zero] using zig_pair_map N 0 n
  have pairs := pairs_perm (List.range n) id (fun i => N-i)
  simp only [List.map_id] at pairs
  dsimp only [id] at pairs
  have hp := pairs.trans ((List.Perm.refl _).append (descending_band N n (by dsimp only [n]; omega)))
  by_cases even : N%2=0
  · have shape : zigList N=(List.range n).flatMap (fun i => [i,N-i])++[n] := by
      dsimp only [zigList]
      rw [show N+1=2*n+1 by dsimp only [n]; omega,List.range_succ,List.map_append,base]
      have hn : zig N (2*n)=n := by dsimp only [zig]; rw [ite_eq_left (by omega)]; omega
      simp only [List.map_cons,List.map_nil,hn]
    rw [shape]
    apply List.perm_iff_count.mpr
    intro x
    rw [List.count_append,hp.count_eq x]
    simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,count_band,Nat.beq_eq_true_eq]
    dsimp only [n]
    repeat (any_goals (first | omega | split))
  · have shape : zigList N=(List.range n).flatMap (fun i => [i,N-i]) := by
      dsimp only [zigList]
      rw [show N+1=2*n by dsimp only [n]; omega,base]
    rw [shape]
    apply hp.trans
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.count_append,List.count_range,count_band]
    dsimp only [n]
    repeat (any_goals (first | omega | split))

theorem zig_edge (N i : Nat) (hi : i<N) : distance (zig N i) (zig N (i+1))=N-i := by
  dsimp only [zig,distance]
  repeat (any_goals (first | omega | split))

theorem zig_edge_cross (N i : Nat) (hi : i<N) : cross (N/2) (zig N i) (zig N (i+1)) := by
  dsimp only [zig,cross]
  repeat (any_goals (first | omega | split))

theorem zig_prefix_edges (N j n : Nat) (hn : j+n≤N) :
    edgeDiffs ((List.range' j (n+1)).map (zig N))=(List.range' j n).map (fun i => N-i) := by
  induction n generalizing j with
  | zero => simp [List.range',edgeDiffs]
  | succ n ih =>
    rw [List.range'_succ]
    simp only [List.map_cons]
    have shape : edgeDiffs (zig N j::(List.range' (j+1) (n+1)).map (zig N))=
      distance (zig N j) (zig N (j+1))::edgeDiffs ((List.range' (j+1) (n+1)).map (zig N)) := by
      rw [List.range'_succ]; simp only [List.map_cons,edgeDiffs]
    rw [shape,zig_edge N j (by omega),ih (j+1) (by omega)]
    simp only [List.range'_succ,List.map_cons]

theorem zig_differences (N : Nat) : (edgeDiffs (zigList N)).Perm (List.range' 1 N) := by
  have hp : edgeDiffs (zigList N)=(List.range N).map (fun i => N-i) := by
    simpa only [zigList,List.range_eq_range',Nat.zero_add] using zig_prefix_edges N 0 N (by omega)
  by_cases zero : N=0
  · subst N; rw [hp]; decide
  · rw [hp]
    simpa only [Nat.sub_self,Nat.zero_add] using descending_band N N (by omega)

theorem crosses_from_lookup (A : Nat) (c : List Nat)
    (h : ∀i,i+1<c.length → cross A (c.getD i 0) (c.getD (i+1) 0)) : crosses A c := by
  induction c using crosses.induct with
  | case1 => trivial
  | case2 a => trivial
  | case3 a b c ih =>
    constructor
    · simpa only [List.getD_cons_zero,List.getD_cons_succ,cross] using h 0 (by simp)
    · apply ih
      intro i hi
      simpa only [List.getD_cons_succ] using h (i+1) (by simp only [List.length_cons] at hi ⊢; omega)

theorem zig_crosses (N : Nat) : crosses (N/2) (zigList N) := by
  apply crosses_from_lookup
  intro i hi
  have len : (zigList N).length=N+1 := by simp [zigList]
  have hi0 : i<N+1 := by omega
  have hi1 : i+1<N+1 := by omega
  have h0 : (zigList N).getD i 0=zig N i := by
    simp only [zigList,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hi0,Option.map_some,Option.getD_some]
  have h1 : (zigList N).getD (i+1) 0=zig N (i+1) := by
    simp only [zigList,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hi1,Option.map_some,Option.getD_some]
  rw [h0,h1]
  exact zig_edge_cross N i (by omega)

theorem zig_first (N : Nat) : (zigList N).head?=some 0 := by simp [zigList,List.head?_eq_getElem?,zig]
theorem zig_last (N : Nat) : (zigList N).getLast?=some (zig N N) := by
  rw [List.getLast?_eq_getElem?]
  simp only [zigList,List.length_map,List.length_range]
  simp only [Nat.add_sub_cancel,List.getElem?_map,List.getElem?_range (by omega : N<N+1),Option.map_some]

end GracefulBoundary.EvenUniform
