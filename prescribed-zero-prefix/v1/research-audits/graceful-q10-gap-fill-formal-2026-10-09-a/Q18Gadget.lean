import VariableSpider
namespace GracefulBoundary.Variable.Q18
set_option maxHeartbeats 1000000

inductive Gadget where
  | g30
  deriving DecidableEq

def pre : Gadget → List Nat
  | .g30 => [3,6,11,16]
def before : Gadget → List Nat
  | .g30 => [18,18,17,17,15,16,14,15,13,13,12,12,10,9,11,10,8,8,5,5,7,7,4,2,3,4]
def after : Gadget → List Nat
  | .g30 => [1,1,2,6,9,14]

def delta (g : Gadget) := (pre g).length+(before g).length

def bump18 (x : Nat) := if x=0 then 0 else x+18

def surgery (g : Gadget) (u v : List Nat) :=
  pre g ++ u.map bump18 ++ before g ++ [0,0] ++ after g ++ v.map bump18

def inserted (g : Gadget) :=
  edgeSums (pre g ++ [21]) ++ edgeSums (22::before g ++ [0]) ++ edgeSums (0::after g ++ [19])

theorem gadget_inserted (g : Gadget) : (inserted g).Perm (List.range' 1 37 ++ [40]) := by
  cases g <;> decide

theorem gadget_lengths (g : Gadget) :
    (pre g).length%2=0 ∧ (before g).length%2=0 ∧ (after g).length%2=0 ∧
    (pre g).length+(before g).length+(after g).length=36 ∧
    4 ≤ delta g ∧ delta g ≤ 30 ∧ delta g%2=0 := by
  cases g <;> decide

theorem gadget_boundaries (g : Gadget) :
    (pre g).head?=some 3 ∧ (before g).getLast?=some 4 ∧ (after g).head?=some 1 := by
  cases g <;> decide

theorem surgery_highs (g : Gadget) (u v : List Nat) (hu : u.length%2=1) :
    (highs (surgery g u v)).Perm ((highs (u++[0,0]++v)).map bump18 ++ List.range' 1 18) := by
  cases g <;> apply List.perm_iff_count.mpr <;> intro x <;>
    simp [surgery,pre,before,after,List.append_assoc,highs_append,highs_map,lows_map,hu,
      lows,bump18,List.count_cons,List.range',List.count_append] <;> omega

theorem surgery_lows (g : Gadget) (u v : List Nat) (hu : u.length%2=1) :
    (lows (surgery g u v)).Perm ((lows (u++[0,0]++v)).map bump18 ++ List.range' 1 18) := by
  cases g <;> apply List.perm_iff_count.mpr <;> intro x <;>
    simp [surgery,pre,before,after,List.append_assoc,lows_append,highs_map,lows_map,hu,
      highs,bump18,List.count_cons,List.range',List.count_append] <;> omega



theorem bump18_positive (x : Nat) (hx : 0 < x) : bump18 x=x+18 := by simp [bump18,Nat.ne_of_gt hx]

theorem map_bump18_positive (c : List Nat) (h : ∀ x ∈ c,0<x) :
    c.map bump18=c.map (fun x => x+18) := by
  apply List.map_congr_left
  intro x hx
  exact bump18_positive x (h x hx)

theorem edgeSums_shift18 (c : List Nat) :
    edgeSums (c.map (fun x => x+18))=(edgeSums c).map (fun x => x+36) := by
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
    edgeSums (22::before g ++ [0,0] ++ after g ++ [19]) =
      edgeSums (22::before g ++ [0]) ++ [0] ++ edgeSums (0::after g ++ [19]) := by
  cases g <;> decide

theorem surgery_sums (g : Gadget) (u v : List Nat)
    (hu0 : u.head?=some 3) (hu4 : u.getLast?=some 4) (hv1 : v.head?=some 1)
    (hup : ∀ x ∈ u,0<x) (hvp : ∀ x ∈ v,0<x) :
    (edgeSums (surgery g u v)).Perm
      ((edgeSums u ++ edgeSums v).map (fun x => x+36) ++ [0] ++ inserted g) := by
  have huhead : (u.map (fun x => x+18)).head?=some 21 := by simp [List.head?_map,hu0]
  have hulast : (u.map (fun x => x+18)).getLast?=some 22 := by simp [List.getLast?_map,hu4]
  have hvhead : (v.map (fun x => x+18)).head?=some 19 := by simp [List.head?_map,hv1]
  unfold surgery
  rw [map_bump18_positive u hup,map_bump18_positive v hvp]
  have hrhead : (u.map (fun x => x+18) ++ before g ++ [0,0] ++ after g ++ v.map (fun x => x+18)).head?=some 21 := by
    simp only [List.head?_append,huhead]; rfl
  rw [show pre g ++ u.map (fun x => x+18) ++ before g ++ [0,0] ++ after g ++ v.map (fun x => x+18) =
    pre g ++ (u.map (fun x => x+18) ++ before g ++ [0,0] ++ after g ++ v.map (fun x => x+18)) by simp only [List.append_assoc]]
  rw [edgeSums_right_head _ _ 21 hrhead]
  have hinner : u.map (fun x => x+18) ++ before g ++ [0,0] ++ after g ++ v.map (fun x => x+18) =
    u.map (fun x => x+18) ++ (before g ++ [0,0] ++ after g ++ v.map (fun x => x+18)) := by simp only [List.append_assoc]
  rw [hinner,edgeSums_left_last _ _ 22 hulast]
  rw [show 22::(before g ++ [0,0] ++ after g ++ v.map (fun x => x+18)) =
    (22::before g ++ [0,0] ++ after g) ++ v.map (fun x => x+18) by simp only [List.cons_append,List.append_assoc]]
  rw [edgeSums_right_head _ _ 19 hvhead,middle_edges,edgeSums_shift18,edgeSums_shift18,List.map_append]
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,inserted]
  omega

end GracefulBoundary.Variable.Q18
