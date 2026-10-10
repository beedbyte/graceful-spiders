import K32Full
namespace GracefulBoundary.FullFixed34

def core12 : List Nat := [3,3,1,2,8,9,12,12,11,5,2,0,0,1,4,4,5,6,6,7,7,8,10,10,9,13,13,14,14,11]
def core14 : List Nat := [3,3,1,2,5,4,6,5,7,7,9,6,2,0,0,1,4,9,8,13,12,12,14,14,13,10,10,8,11,11]

theorem core12_valid : FixedDepth.CorePair 15 12 13 core12 := by
  constructor
  · unfold BoundaryCore; decide
  all_goals decide
theorem core14_valid : FixedDepth.CorePair 15 14 15 core14 := by
  constructor
  · unfold BoundaryCore; decide
  all_goals decide

theorem core12_path_certificate : Even.Certificate 15 12 13 (Even.completePath 15 core12) :=
  Even.core_pair_to_certificate 15 12 13 core12 core12_valid
theorem core14_path_certificate : Even.Certificate 15 14 15 (Even.completePath 15 core14) :=
  Even.core_pair_to_certificate 15 14 15 core14 core14_valid

/-- Actual midpoint-alpha path: every label/edge weight, cut and midpoint are supplied by the proved shell bridge. -/
theorem core12_actual_alpha_path : Graceful (pathGraph 68) (68) (pathLabel 68 (Even.completePath 15 core12)) ∧
    Alpha (pathGraph 68) 34 (pathLabel 68 (Even.completePath 15 core12)) := by
  have hc := (Even.boundary_shell_bridge 15 core12 core12_valid.boundary)
  exact ⟨list_path_graceful 68 _ hc.2.1 hc.2.2.1,list_path_alpha 68 34 _ hc.1 hc.2.2.2.1⟩
theorem core14_actual_alpha_path : Graceful (pathGraph 68) (68) (pathLabel 68 (Even.completePath 15 core14)) ∧
    Alpha (pathGraph 68) 34 (pathLabel 68 (Even.completePath 15 core14)) := by
  have hc := (Even.boundary_shell_bridge 15 core14 core14_valid.boundary)
  exact ⟨list_path_graceful 68 _ hc.2.1 hc.2.2.1,list_path_alpha 68 34 _ hc.1 hc.2.2.2.1⟩

/-- Universal actual two-arm-alpha/residual transfer, including n2,m0 and n2,m1. -/
theorem k34_depth12_and13 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃f : SpiderVertex n m 34 → Nat, Graceful (spiderGraph n m 34) (n*34+m) f ∧ f (.arm a ⟨11,by decide⟩)=0) ∧
    (∃f : SpiderVertex n m 34 → Nat, Graceful (spiderGraph n m 34) (n*34+m) f ∧ f (.arm a ⟨12,by decide⟩)=0) :=
  Even.core_pair_spider_transfer 15 12 13 n m core12 core12_valid hn a
theorem k34_depth14_and15 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃f : SpiderVertex n m 34 → Nat, Graceful (spiderGraph n m 34) (n*34+m) f ∧ f (.arm a ⟨13,by decide⟩)=0) ∧
    (∃f : SpiderVertex n m 34 → Nat, Graceful (spiderGraph n m 34) (n*34+m) f ∧ f (.arm a ⟨14,by decide⟩)=0) :=
  Even.core_pair_spider_transfer 15 14 15 n m core14 core14_valid hn a

end GracefulBoundary.FullFixed34
