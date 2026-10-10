import UniversalTip
namespace GracefulBoundary.LowBand
open EvenBoundary EvenBoundary.Flexible

theorem named_prefix (R n m d : Nat) (hR : 18≤R) (hn : 2≤n)
    (a : Fin n) (hd : 2≤d) (_hlt : d<2*R) (hprefix : d≤GapFill.depthPrefix (2*R)) :
    NamedDepthZero R n m d a :=
  GapFill.all_lengths_prefix_zero (2*R) n m d (by omega) hn a ⟨hd,hprefix⟩

/-- Only the source family and numeric D8 half-length bound remain premises. -/
theorem all_interior (R n m : Nat) (hR : 18≤R) (hn : 2≤n)
    (hD : R≤GapFill.depthPrefix (2*R)) (hfamily : OddSourceFamily) :
    ∀(a : Fin n)(d : Nat),2≤d → d<2*R → NamedDepthZero R n m d a :=
  all_interior_from_source_shells R (GapFill.depthPrefix (2*R)) n m hR hn hD
    (fun a d => named_prefix R n m d hR hn a)
    (fun a d => named_low_deficit R n m d hR hn a)
    hfamily all_canonical_grafts

/-- Complete case split over actual named vertices, with the two remaining gates explicit. -/
theorem full_actual_if_sources_and_D8 (R n m : Nat) (hR : 18≤R) (hn : 2≤n)
    (hD : R≤GapFill.depthPrefix (2*R)) (hfamily : OddSourceFamily)
    (v : SpiderVertex n m (2*R)) :
    ∃f : SpiderVertex n m (2*R) → Nat, Graceful (spiderGraph n m (2*R)) (n*(2*R)+m) f ∧ f v=0 := by
  cases v with
  | center => exact FullFixed.center_zero R n m (by omega)
  | leaf a => exact FullFixed.short_leaf_zero R n m (by omega) a
  | arm a d =>
    by_cases one : d.val=0
    · have eq : d=⟨0,by omega⟩ := Fin.ext one
      rw [eq]; exact FullFixed.depth_one_zero R n m (by omega) hn a
    by_cases last : d.val=2*R-1
    · have eq : d=⟨2*R-1,by omega⟩ := Fin.ext last
      rw [eq]; exact actual_tip_zero R n m (by omega) (by omega) a
    obtain ⟨hlt,f,hf,hzero⟩ := all_interior R n m hR hn hD hfamily a (d.val+1) (by omega) (by omega)
    have eq : (⟨d.val+1-1,hlt⟩ : Fin (2*R))=d := Fin.ext (by dsimp only; omega)
    rw [eq] at hzero
    exact ⟨f,hf,hzero⟩

theorem no_two_distinct_zeros (R n m : Nat) (f : SpiderVertex n m (2*R) → Nat)
    (hf : Graceful (spiderGraph n m (2*R)) (n*(2*R)+m) f)
    (v w : SpiderVertex n m (2*R)) (hvw : v≠w) : ¬(f v=0 ∧ f w=0) := by
  intro h
  exact hvw (hf.vertices.injective v w (h.1.trans h.2.symm))

theorem radius17_not_in_bridge_range : ¬(18≤(17:Nat) ∧ 17≤22) := by decide

end GracefulBoundary.LowBand
