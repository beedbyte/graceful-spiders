import ThirdSpider
namespace GracefulBoundary.Variable

inductive Gadget where
  | g4 | g6 | g8 | g10 | g12 | g14
  deriving DecidableEq

def pre : Gadget → List Nat
  | .g4 => [3,6] | .g6 => [3,5,6,6] | .g8 => [3,6]
  | .g10 => [3,7] | .g12 => [3,6] | .g14 => [3,7]
def before : Gadget → List Nat
  | .g4 => [9,4] | .g6 => [9,4] | .g8 => [9,7,5,8,7,4]
  | .g10 => [9,9,6,5,4,2,3,4] | .g12 => [9,8,5,6,8,7,3,2,4,4]
  | .g14 => [9,9,8,8,6,7,5,6,3,2,4,4]
def after : Gadget → List Nat
  | .g4 => [1,1,2,5,3,2,4,6,5,7,7,8,8,9]
  | .g6 => [1,1,2,5,4,2,3,7,7,8,8,9]
  | .g8 => [1,1,2,5,3,2,4,6,8,9]
  | .g10 => [1,1,2,6,8,8,5,7]
  | .g12 => [1,1,2,5,7,9] | .g14 => [1,1,2,5]
def delta (g : Gadget) := (pre g).length+(before g).length

def bump9 (x : Nat) := if x=0 then 0 else x+9

def surgery (g : Gadget) (u v : List Nat) :=
  pre g ++ u.map bump9 ++ before g ++ [0,0] ++ after g ++ v.map bump9

def inserted (g : Gadget) :=
  edgeSums (pre g ++ [12]) ++ edgeSums (13::before g ++ [0]) ++ edgeSums (0::after g ++ [10])

theorem gadget_inserted (g : Gadget) : (inserted g).Perm (List.range' 1 19 ++ [22]) := by
  cases g <;> decide

theorem gadget_lengths (g : Gadget) :
    (pre g).length%2=0 ∧ (before g).length%2=0 ∧ (after g).length%2=0 ∧
    (pre g).length+(before g).length+(after g).length=18 ∧
    4 ≤ delta g ∧ delta g ≤ 14 ∧ delta g%2=0 := by
  cases g <;> decide

theorem gadget_boundaries (g : Gadget) :
    (pre g).head?=some 3 ∧ (before g).getLast?=some 4 ∧ (after g).head?=some 1 := by
  cases g <;> decide

theorem surgery_highs (g : Gadget) (u v : List Nat) (hu : u.length%2=1) :
    (highs (surgery g u v)).Perm ((highs (u++[0,0]++v)).map bump9 ++ List.range' 1 9) := by
  cases g <;> apply List.perm_iff_count.mpr <;> intro x <;>
    simp [surgery,pre,before,after,List.append_assoc,highs_append,highs_map,lows_map,hu,
      lows,bump9,List.count_cons,List.range',List.count_append] <;> omega

theorem surgery_lows (g : Gadget) (u v : List Nat) (hu : u.length%2=1) :
    (lows (surgery g u v)).Perm ((lows (u++[0,0]++v)).map bump9 ++ List.range' 1 9) := by
  cases g <;> apply List.perm_iff_count.mpr <;> intro x <;>
    simp [surgery,pre,before,after,List.append_assoc,lows_append,highs_map,lows_map,hu,
      highs,bump9,List.count_cons,List.range',List.count_append] <;> omega



theorem bump9_positive (x : Nat) (hx : 0 < x) : bump9 x=x+9 := by simp [bump9,Nat.ne_of_gt hx]

theorem map_bump9_positive (c : List Nat) (h : ∀ x ∈ c,0<x) :
    c.map bump9=c.map (fun x => x+9) := by
  apply List.map_congr_left
  intro x hx
  exact bump9_positive x (h x hx)

theorem edgeSums_shift9 (c : List Nat) :
    edgeSums (c.map (fun x => x+9))=(edgeSums c).map (fun x => x+18) := by
  induction c using edgeSums.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b xs ih =>
    simp only [List.map_cons,edgeSums]
    congr 1
    omega

theorem edgeSums_right_head (u v : List Nat) (b : Nat) (hv : v.head?=some b) :
    edgeSums (u++v)=edgeSums (u++[b]) ++ edgeSums v := by
  obtain ⟨vs,rfl⟩ := List.head?_eq_some_iff.mp hv
  exact edgeSums_overlap u b vs

theorem edgeSums_left_last (u v : List Nat) (a : Nat) (hu : u.getLast?=some a) :
    edgeSums (u++v)=edgeSums u ++ edgeSums (a::v) := by
  cases v with
  | nil => simp [edgeSums]
  | cons b v => exact edgeSums_join u a b v hu

theorem middle_edges (g : Gadget) :
    edgeSums (13::before g ++ [0,0] ++ after g ++ [10]) =
      edgeSums (13::before g ++ [0]) ++ [0] ++ edgeSums (0::after g ++ [10]) := by
  cases g <;> decide

theorem surgery_sums (g : Gadget) (u v : List Nat)
    (hu0 : u.head?=some 3) (hu4 : u.getLast?=some 4) (hv1 : v.head?=some 1)
    (hup : ∀ x ∈ u,0<x) (hvp : ∀ x ∈ v,0<x) :
    (edgeSums (surgery g u v)).Perm
      ((edgeSums u ++ edgeSums v).map (fun x => x+18) ++ [0] ++ inserted g) := by
  have huhead : (u.map (fun x => x+9)).head?=some 12 := by simp [List.head?_map,hu0]
  have hulast : (u.map (fun x => x+9)).getLast?=some 13 := by simp [List.getLast?_map,hu4]
  have hvhead : (v.map (fun x => x+9)).head?=some 10 := by simp [List.head?_map,hv1]
  unfold surgery
  rw [map_bump9_positive u hup,map_bump9_positive v hvp]
  have hrhead : (u.map (fun x => x+9) ++ before g ++ [0,0] ++ after g ++ v.map (fun x => x+9)).head?=some 12 := by
    simp only [List.head?_append,huhead]; rfl
  rw [show pre g ++ u.map (fun x => x+9) ++ before g ++ [0,0] ++ after g ++ v.map (fun x => x+9) =
    pre g ++ (u.map (fun x => x+9) ++ before g ++ [0,0] ++ after g ++ v.map (fun x => x+9)) by simp only [List.append_assoc]]
  rw [edgeSums_right_head _ _ 12 hrhead]
  have hinner : u.map (fun x => x+9) ++ before g ++ [0,0] ++ after g ++ v.map (fun x => x+9) =
    u.map (fun x => x+9) ++ (before g ++ [0,0] ++ after g ++ v.map (fun x => x+9)) := by simp only [List.append_assoc]
  rw [hinner,edgeSums_left_last _ _ 13 hulast]
  rw [show 13::(before g ++ [0,0] ++ after g ++ v.map (fun x => x+9)) =
    (13::before g ++ [0,0] ++ after g) ++ v.map (fun x => x+9) by simp only [List.cons_append,List.append_assoc]]
  rw [edgeSums_right_head _ _ 10 hvhead,middle_edges,edgeSums_shift9,edgeSums_shift9,List.map_append]
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,inserted]
  omega

end GracefulBoundary.Variable
