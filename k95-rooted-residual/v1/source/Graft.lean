import Residual
namespace GracefulBoundary

def boundaryCenter (s : Nat) : Fin (12*s+7) := ⟨6*s+3,by omega⟩
def boundaryZero (s : Nat) : Fin (12*s+7) := ⟨2*s+3,by omega⟩
def boundaryMaximum (s : Nat) : Fin (12*s+7) := ⟨2*s+2,by omega⟩

abbrev BoundaryGraftVertex (s h m : Nat) :=
  GraftVertices (Fin (12*s+7)) (SpiderVertex h m (6*s+3)) (boundaryCenter s)

noncomputable def boundaryGraftGraph (s h m : Nat) :=
  graftGraph (pathGraph (12*s+6)) (spiderGraph h m (6*s+3)) (boundaryCenter s) SpiderVertex.center

def boundaryGraftLabel (s h m : Nat) (c : List Nat) : BoundaryGraftVertex s h m → Nat :=
  graftLabel (boundaryCenter s) (pathLabel (12*s+6) c) (residualLabel h m (6*s+3))
    (6*s+2) (h*(6*s+3)+m)

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

end GracefulBoundary
