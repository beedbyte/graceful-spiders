import ThirdShell
namespace GracefulBoundary.ThirdPair

def boundaryZero (s : Nat) : Fin (12*s+7) := ⟨2*s-1,by omega⟩
def boundaryMaximum (s : Nat) : Fin (12*s+7) := ⟨2*s-2,by omega⟩
theorem certificate_graft (s h m : Nat) (c : List Nat) (hc : PathCertificate s c) :
    Graceful (boundaryGraftGraph s h m) (12*s+6+(h*(6*s+3)+m)) (boundaryGraftLabel s h m c) := by
  have hp := certificate_graph s c hc
  have ha := certificate_graph_anchors s c hc
  have hr := residual_gracefulness h m (3*s+1)
  have hk : 2*(3*s+1)+1=6*s+3 := by omega
  rw [hk] at hr
  exact graceful_graft (pathGraph (12*s+6)) (spiderGraph h m (6*s+3))
    (boundaryCenter s) SpiderVertex.center (pathLabel (12*s+6) c) (residualLabel h m (6*s+3))
    (6*s+2) (12*s+6) (h*(6*s+3)+m) hp.1 hr ha.1 rfl hp.2

theorem certificate_graft_anchors (s h m : Nat) (c : List Nat) (hc : PathCertificate s c) :
    boundaryGraftLabel s h m c (graftEmbed (boundaryCenter s) SpiderVertex.center (boundaryZero s))=0 ∧
    boundaryGraftLabel s h m c (graftEmbed (boundaryCenter s) SpiderVertex.center (boundaryMaximum s))=
      12*s+6+(h*(6*s+3)+m) := by
  have ha := certificate_graph_anchors s c hc
  constructor
  · exact graft_zero_anchor (boundaryCenter s) SpiderVertex.center (pathLabel (12*s+6) c)
      (residualLabel h m (6*s+3)) (6*s+2) (h*(6*s+3)+m) ha.1 rfl (boundaryZero s) ha.2.1
  · exact graft_max_anchor (boundaryCenter s) SpiderVertex.center (pathLabel (12*s+6) c)
      (residualLabel h m (6*s+3)) (6*s+2) (12*s+6) (h*(6*s+3)+m) ha.1 rfl
      (by omega) (boundaryMaximum s) ha.2.2

/-- Fully discharged graceful existence on the explicit graft graph.
    Identifying this vertex/edge type with the requested spider is the next task. -/
theorem uniform_boundary_grafts (s h m : Nat) (hs : 2 ≤ s) :
    ∃ f : BoundaryGraftVertex s h m → Nat,
      Graceful (boundaryGraftGraph s h m) (12*s+6+(h*(6*s+3)+m)) f ∧
      f (graftEmbed (boundaryCenter s) SpiderVertex.center (boundaryZero s))=0 ∧
      f (graftEmbed (boundaryCenter s) SpiderVertex.center (boundaryMaximum s))=
        12*s+6+(h*(6*s+3)+m) := by
  obtain ⟨c,hc⟩ := uniform_midpoint_alpha_paths s hs
  exact ⟨boundaryGraftLabel s h m c,certificate_graft s h m c hc,certificate_graft_anchors s h m c hc⟩


theorem zero_anchor_identification (s h m : Nat) (hs : 2 ≤ s) :
    spiderToGraft s h m (.arm ⟨0,by omega⟩ ⟨4*s+3,by omega⟩) =
      graftEmbed (boundaryCenter s) SpiderVertex.center (boundaryZero s) := by
  simp only [spiderToGraft,dite_true]
  have he : boundaryZero s = (leftVertex s ⟨4*s+3,by omega⟩).val := by
    apply Fin.ext; dsimp only [boundaryZero,leftVertex]; omega
  rw [he,embed_left]

theorem maximum_anchor_identification (s h m : Nat) (hs : 2 ≤ s) :
    spiderToGraft s h m (.arm ⟨0,by omega⟩ ⟨4*s+4,by omega⟩) =
      graftEmbed (boundaryCenter s) SpiderVertex.center (boundaryMaximum s) := by
  simp only [spiderToGraft,dite_true]
  have he : boundaryMaximum s = (leftVertex s ⟨4*s+4,by omega⟩).val := by
    apply Fin.ext; dsimp only [boundaryMaximum,leftVertex]; omega
  rw [he,embed_left]

theorem uniform_first_arm_spiders (s h m : Nat) (hs : 2 ≤ s) :
    ∃ f : SpiderVertex (h+2) m (6*s+3) → Nat,
      Graceful (spiderGraph (h+2) m (6*s+3)) ((h+2)*(6*s+3)+m) f ∧
      f (.arm ⟨0,by omega⟩ ⟨4*s+3,by omega⟩)=0 ∧
      f (.arm ⟨0,by omega⟩ ⟨4*s+4,by omega⟩)=((h+2)*(6*s+3)+m) := by
  obtain ⟨f,hf,hzero,hmax⟩ := uniform_boundary_grafts s h m hs
  have hg := graft_graceful_on_spider s h m _ f hf
  have hm : 12*s+6+(h*(6*s+3)+m)=(h+2)*(6*s+3)+m := by
    simp only [Nat.add_mul]; omega
  rw [hm] at hg hmax
  refine ⟨fun v => f (spiderToGraft s h m v),hg,?_,?_⟩
  · dsimp only; rw [zero_anchor_identification s h m hs]; exact hzero
  · dsimp only; rw [maximum_anchor_identification s h m hs]; exact hmax


theorem uniform_selected_arm_anchors (s n m : Nat) (hs : 2 ≤ s) (hn : 2 ≤ n) (a : Fin n) :
    ∃ f : SpiderVertex n m (6*s+3) → Nat,
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) f ∧
      f (.arm a ⟨4*s+3,by omega⟩)=0 ∧
      f (.arm a ⟨4*s+4,by omega⟩)=n*(6*s+3)+m := by
  obtain ⟨h,rfl⟩ : ∃ h,n=h+2 := ⟨n-2,by omega⟩
  obtain ⟨f,hf,hzero,hmax⟩ := uniform_first_arm_spiders s h m hs
  let z : Fin (h+2) := ⟨0,by omega⟩
  refine ⟨fun v => f (swapVertex a z v),graceful_swap a z f hf,?_,?_⟩
  · simpa only [swapVertex,swapIndex_first] using hzero
  · simpa only [swapVertex,swapIndex_first] using hmax

/-- Unconditional third-pair prescribed-zero theorem on the actual indexed
    spider, for every number of short leaves and every requested long arm. -/
theorem third_pair_prescribed_zero (s n m : Nat) (hs : 2 ≤ s) (hn : 2 ≤ n) (a : Fin n) :
    (∃ f : SpiderVertex n m (6*s+3) → Nat,
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) f ∧
      f (.arm a ⟨4*s+3,by omega⟩)=0) ∧
    (∃ g : SpiderVertex n m (6*s+3) → Nat,
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) g ∧
      g (.arm a ⟨4*s+4,by omega⟩)=0) := by
  obtain ⟨f,hf,hzero,hmax⟩ := uniform_selected_arm_anchors s n m hs hn a
  constructor
  · exact ⟨f,hf,hzero⟩
  · refine ⟨fun v => n*(6*s+3)+m-f v,graceful_complement _ _ f hf,?_⟩
    simp only [hmax,Nat.sub_self]

/-- Same result with an explicitly supplied permitted one-based depth. -/
theorem third_pair_at_depth (s n m d : Nat) (hs : 2 ≤ s) (hn : 2 ≤ n)
    (hd : d=4*s+4 ∨ d=4*s+5) (a : Fin n) :
    ∃ (hlt : d-1 < 6*s+3) (f : SpiderVertex n m (6*s+3) → Nat),
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 := by
  have hh := third_pair_prescribed_zero s n m hs hn a
  cases hd with
  | inl hd => subst d; exact ⟨by omega,hh.1⟩
  | inr hd =>
    subst d
    have he : 4*s+5-1=4*s+4 := by omega
    simpa only [he] using (show ∃ (hlt : 4*s+4 < 6*s+3) (f : SpiderVertex n m (6*s+3) → Nat),
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) f ∧ f (.arm a ⟨4*s+4,hlt⟩)=0 from ⟨by omega,hh.2⟩)



end GracefulBoundary.ThirdPair

namespace GracefulBoundary
/-- Six boundary depths, with the labeling chosen for the requested vertex. -/
theorem six_depths_prescribed_zero (s n m d : Nat) (hs : 2 ≤ s) (hn : 2 ≤ n)
    (hd : d=4*s ∨ d=4*s+1 ∨ d=4*s+2 ∨ d=4*s+3 ∨ d=4*s+4 ∨ d=4*s+5)
    (a : Fin n) :
    ∃ (hlt : d-1 < 6*s+3) (f : SpiderVertex n m (6*s+3) → Nat),
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 := by
  rcases hd with h0 | h1 | h2 | h3 | h4 | h5
  · exact four_depths_prescribed_zero s n m d hs hn (Or.inl h0) a
  · exact four_depths_prescribed_zero s n m d hs hn (Or.inr (Or.inl h1)) a
  · exact four_depths_prescribed_zero s n m d hs hn (Or.inr (Or.inr (Or.inl h2))) a
  · exact four_depths_prescribed_zero s n m d hs hn (Or.inr (Or.inr (Or.inr h3))) a
  · exact ThirdPair.third_pair_at_depth s n m d hs hn (Or.inl h4) a
  · exact ThirdPair.third_pair_at_depth s n m d hs hn (Or.inr h5) a
end GracefulBoundary
