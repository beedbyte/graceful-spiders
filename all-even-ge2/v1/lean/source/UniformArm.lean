import AnchoredAlpha
namespace GracefulBoundary.EvenUniform
open FixedEven

def cut (n r : Nat) := n*r
def bridge (n r : Nat) := ((n+1)/2)*(2*r)
def armList (n r : Nat) :=
  (if n%2=0 then zigList (2*r-1) else (zigList (2*r-1)).reverse).map (fun x => cut n r+1+x)
def armLabel (n r : Nat) (d : Fin (2*r)) := (armList n r).getD d.val 0

theorem cut_positive (n r : Nat) (hn : 1≤n) (hr : 1≤r) : 1≤cut n r := by
  have h := Nat.mul_le_mul_right r hn
  simp only [Nat.one_mul] at h
  dsimp only [cut]; omega

theorem bridge_at_cut (n r : Nat) :
    bridge n r=if n%2=0 then cut n r else cut n r+r := by
  by_cases even : n%2=0
  · have h : (n+1)/2=n/2 := by omega
    have eq : n=2*(n/2) := by omega
    dsimp only [bridge,cut]
    rw [ite_eq_left even,h]
    conv => rhs; rw [eq]
    simp only [Nat.mul_assoc,Nat.mul_left_comm]
  · have h : (n+1)/2=n/2+1 := by omega
    have eq : n=2*(n/2)+1 := by omega
    dsimp only [bridge,cut]
    rw [ite_eq_right even,h]
    conv => rhs; rw [eq]
    simp only [Nat.add_mul,Nat.one_mul,Nat.mul_assoc,Nat.mul_left_comm]
    omega

theorem bridge_bounds (n r : Nat) (hn : 2≤n) : 2*r≤bridge n r ∧ bridge n r≤n*(2*r) := by
  have lo := Nat.mul_le_mul_right (2*r) (show 1≤(n+1)/2 by omega)
  have hi := Nat.mul_le_mul_right (2*r) (show (n+1)/2≤n by omega)
  simp only [Nat.one_mul] at lo
  exact ⟨lo,hi⟩

theorem bridge_next_bounds (n r : Nat) : bridge n r≤bridge (n+1) r ∧ bridge (n+1) r≤bridge n r+2*r := by
  have lo := Nat.mul_le_mul_right (2*r) (show (n+1)/2≤(n+1+1)/2 by omega)
  have hi := Nat.mul_le_mul_right (2*r) (show (n+1+1)/2≤(n+1)/2+1 by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hi
  exact ⟨lo,hi⟩

theorem bridge_next (n r : Nat) : bridge (n+1) r=if n%2=0 then bridge n r+2*r else bridge n r := by
  by_cases even : n%2=0
  · have eq : (n+1+1)/2=(n+1)/2+1 := by omega
    simp only [bridge,eq,even,ite_true,Nat.add_mul,Nat.one_mul]
  · have eq : (n+1+1)/2=(n+1)/2 := by omega
    simp only [bridge,eq,even,ite_false]

theorem arm_list_length (n r : Nat) (hr : 1≤r) : (armList n r).length=2*r := by
  dsimp only [armList]
  split <;> simp only [List.length_map,List.length_reverse,zigList,List.length_map,List.length_range] <;> omega

theorem arm_list_labels (n r : Nat) (hr : 1≤r) : (armList n r).Perm (List.range' (cut n r+1) (2*r)) := by
  have hp : (if n%2=0 then zigList (2*r-1) else (zigList (2*r-1)).reverse).Perm (List.range (2*r)) := by
    have hh : (zigList (2*r-1)).Perm (List.range (2*r)) := by simpa only [show 2*r-1+1=2*r by omega] using zig_labels (2*r-1)
    split
    · exact hh
    · exact (List.reverse_perm _).trans hh
  have hm := hp.map (fun x => cut n r+1+x)
  rw [←List.range'_eq_map_range] at hm
  exact hm

theorem arm_label_band (n r : Nat) (hr : 1≤r) : BandBijection (armLabel n r) (cut n r+1) (cut n r+2*r) :=
  list_band_bijection _ _ _ _ (by omega) (arm_list_labels n r hr)

theorem arm_list_differences (n r : Nat) :
    (edgeDiffs (armList n r)).Perm (List.range' 1 (2*r-1)) := by
  dsimp only [armList]
  rw [LabelOne.translated_edges]
  split
  · exact zig_differences (2*r-1)
  · rw [edgeDiffs_reverse]; exact (List.reverse_perm _).trans (zig_differences (2*r-1))

theorem arm_list_first (n r : Nat) (hr : 1≤r) : (armList n r).head?=some (bridge n r+1) := by
  dsimp only [armList]
  rw [List.head?_map,bridge_at_cut]
  by_cases even : n%2=0
  · rw [ite_eq_left even,ite_eq_left even,zig_first]; rfl
  · rw [ite_eq_right even,ite_eq_right even,List.head?_reverse,zig_last]
    simp only [Option.map_some]
    congr 1
    dsimp only [zig]
    rw [ite_eq_right (by omega)]
    omega

theorem arm_list_crosses (n r : Nat) (hr : 1≤r) : crosses (cut n r+r) (armList n r) := by
  have hh : crosses (r-1) (zigList (2*r-1)) := by simpa only [show (2*r-1)/2=r-1 by omega] using zig_crosses (2*r-1)
  have hs : crosses (r-1) (if n%2=0 then zigList (2*r-1) else (zigList (2*r-1)).reverse) := by
    split
    · exact hh
    · exact crosses_reverse _ _ hh
  have hm := crosses_translate (r-1) (cut n r+1) _ hs
  rw [show cut n r+1+(r-1)=cut n r+r by omega] at hm
  exact hm

theorem list_arm_weights (k B : Nat) (c : List Nat) (hk : 1≤k) (hB : k≤B)
    (hp : c.Perm (B::List.range' 1 (k-1))) : ArmWeights k B (fun d : Fin k => c.getD d.val 0) := by
  have len : c.length=k := by have hh := hp.length_eq; simp only [List.length_cons,List.length_range'] at hh; omega
  have nodup : c.Nodup := by
    apply hp.nodup_iff.mpr
    apply List.nodup_cons.mpr
    constructor
    · intro hm; obtain ⟨i,hi,he⟩ := List.mem_range'.mp hm; omega
    · exact List.nodup_range'
  constructor
  · intro d e he; apply Fin.ext; exact (nodup.getD_inj (by omega) (by omega)).mp he
  · intro d
    have hd : d.val<c.length := by omega
    have hm := hp.mem_iff.mp (List.getElem_mem hd)
    rw [List.getElem_eq_getD (h:=hd) 0] at hm
    simp only [List.mem_cons] at hm
    rcases hm with h|h
    · exact Or.inl h
    · obtain ⟨i,hi,he⟩ := List.mem_range'.mp h; exact Or.inr ⟨by omega,by omega⟩
  · obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (hp.mem_iff.mpr (List.mem_cons_self))
    exact ⟨⟨i,by omega⟩,by rw [←List.getElem_eq_getD (h:=hi) 0]; exact he⟩
  · intro x hx ht
    have hm : x∈B::List.range' 1 (k-1) := List.mem_cons_of_mem B (List.mem_range'.mpr ⟨x-1,by omega,by omega⟩)
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (hp.mem_iff.mpr hm)
    exact ⟨⟨i,by omega⟩,by rw [←List.getElem_eq_getD (h:=hi) 0]; exact he⟩

theorem new_arm_weight_lookup {V E : Type} (G : IndexedGraph V E) (root : V) (g : V → Nat)
    (n r : Nat) (hn : 1≤n) (hr : 1≤r) (hroot : g root=1) (d : Fin (2*r)) :
    weight (FixedEven.graph G root (2*r)) (label g (cut n r) (2*r) (armLabel n r)) (.inr d)=
      (edgeDiffs (1::armList n r)).getD d.val 0 := by
  have len := arm_list_length n r hr
  have lookup := edgeDiffs_lookup (1::armList n r) d.val (by simp only [List.length_cons,len]; have := d.isLt; omega)
  rw [lookup]
  by_cases hd : d.val=0
  · dsimp only [weight,FixedEven.graph,label]
    rw [ite_eq_left hd]
    dsimp only [shift,armLabel]
    rw [hroot,ite_eq_right (by have := cut_positive n r hn hr; omega)]
    simp only [hd,List.getD_cons_zero,List.getD_cons_succ]
  · obtain ⟨j,hj⟩ : ∃j,d.val=j+1 := ⟨d.val-1,by omega⟩
    dsimp only [weight,FixedEven.graph,label]
    rw [ite_eq_right hd]
    dsimp only [armLabel]
    simp only [hj,List.getD_cons_succ,show j+1-1=j by omega]

theorem new_arm_weights {V E : Type} (G : IndexedGraph V E) (root : V) (g : V → Nat)
    (n r : Nat) (hn : 2≤n) (hr : 1≤r) (hroot : g root=1) :
    ArmWeights (2*r) (bridge n r) (fun d => weight (FixedEven.graph G root (2*r)) (label g (cut n r) (2*r) (armLabel n r)) (.inr d)) := by
  have hB := (bridge_bounds n r hn).1
  obtain ⟨tail,shape⟩ := List.head?_eq_some_iff.mp (arm_list_first n r hr)
  have edges : edgeDiffs (1::armList n r)=bridge n r::edgeDiffs (armList n r) := by
    rw [shape]
    simp only [edgeDiffs]
    congr 1
    dsimp only [distance]; omega
  have hp : (edgeDiffs (1::armList n r)).Perm (bridge n r::List.range' 1 (2*r-1)) := by rw [edges]; exact (arm_list_differences n r).cons (bridge n r)
  have hw := list_arm_weights (2*r) (bridge n r) _ (by omega) hB hp
  have eq := funext (new_arm_weight_lookup G root g n r (by omega) hr hroot)
  rw [eq]; exact hw

end GracefulBoundary.EvenUniform
