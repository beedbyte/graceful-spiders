import K30Full
namespace GracefulBoundary.FullFixed32

def core12 : List Nat := [3,3,1,2,8,9,12,11,7,5,2,0,0,1,4,4,5,6,9,7,6,8,11,13,13,12,10,10]
def core14 : List Nat := [3,3,1,2,5,4,6,11,9,5,7,6,2,0,0,1,4,7,8,8,10,9,13,13,12,12,11,10]

theorem core12_valid : FixedDepth.CorePair 14 12 13 core12 := by
  constructor
  · unfold BoundaryCore; decide
  all_goals decide
theorem core14_valid : FixedDepth.CorePair 14 14 15 core14 := by
  constructor
  · unfold BoundaryCore; decide
  all_goals decide

theorem core12_path_certificate : Even.Certificate 14 12 13 (Even.completePath 14 core12) :=
  Even.core_pair_to_certificate 14 12 13 core12 core12_valid
theorem core14_path_certificate : Even.Certificate 14 14 15 (Even.completePath 14 core14) :=
  Even.core_pair_to_certificate 14 14 15 core14 core14_valid

/-- Actual midpoint-alpha path: every label/edge weight, cut and midpoint are supplied by the proved shell bridge. -/
theorem core12_actual_alpha_path : Graceful (pathGraph 64) (64) (pathLabel 64 (Even.completePath 14 core12)) ∧
    Alpha (pathGraph 64) 32 (pathLabel 64 (Even.completePath 14 core12)) := by
  have hc := (Even.boundary_shell_bridge 14 core12 core12_valid.boundary)
  exact ⟨list_path_graceful 64 _ hc.2.1 hc.2.2.1,list_path_alpha 64 32 _ hc.1 hc.2.2.2.1⟩
theorem core14_actual_alpha_path : Graceful (pathGraph 64) (64) (pathLabel 64 (Even.completePath 14 core14)) ∧
    Alpha (pathGraph 64) 32 (pathLabel 64 (Even.completePath 14 core14)) := by
  have hc := (Even.boundary_shell_bridge 14 core14 core14_valid.boundary)
  exact ⟨list_path_graceful 64 _ hc.2.1 hc.2.2.1,list_path_alpha 64 32 _ hc.1 hc.2.2.2.1⟩

/-- Universal actual two-arm-alpha/residual transfer, including n2,m0 and n2,m1. -/
theorem k32_depth12_and13 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃f : SpiderVertex n m 32 → Nat, Graceful (spiderGraph n m 32) (n*32+m) f ∧ f (.arm a ⟨11,by decide⟩)=0) ∧
    (∃f : SpiderVertex n m 32 → Nat, Graceful (spiderGraph n m 32) (n*32+m) f ∧ f (.arm a ⟨12,by decide⟩)=0) :=
  Even.core_pair_spider_transfer 14 12 13 n m core12 core12_valid hn a
theorem k32_depth14_and15 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃f : SpiderVertex n m 32 → Nat, Graceful (spiderGraph n m 32) (n*32+m) f ∧ f (.arm a ⟨13,by decide⟩)=0) ∧
    (∃f : SpiderVertex n m 32 → Nat, Graceful (spiderGraph n m 32) (n*32+m) f ∧ f (.arm a ⟨14,by decide⟩)=0) :=
  Even.core_pair_spider_transfer 14 14 15 n m core14 core14_valid hn a

end GracefulBoundary.FullFixed32
