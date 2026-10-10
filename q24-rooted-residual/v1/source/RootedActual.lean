import RootedCatalog
import RootedInjective

namespace GracefulBoundary.Rooted71

/-- Two new 71-edge arms over any rooted onto-labeled graceful residual.
    `right=false` selects the left new arm; `right=true` selects the right. -/
theorem onto_new_arm {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q : Nat) (hg : Graceful H Q g) (hroot : g root=0)
    (d : Nat) (hd : 1≤d ∧ d≤70) (right : Bool) :
    ∃ f : GraftVertices (Fin 143) W midpoint → Nat,
      Graceful (graftGraph (pathGraph 142) H midpoint root) (142+Q) f ∧
      f (graftEmbed midpoint root (selectedPoint d hd right))=0 := by
  obtain ⟨w,hw,hx⟩ := all_packets d hd right
  exact graft_extreme H root g Q hg hroot w hw (selectedPoint d hd right) hx

/-- Conventional version for a residual graph with injective, possibly non-onto
    vertex labels and all edge differences 1..Q. -/
theorem conventional_new_arm {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q : Nat) (hg : ConventionalGraceful H Q g) (hroot : g root=0)
    (d : Nat) (hd : 1≤d ∧ d≤70) (right : Bool) :
    ∃ f : GraftVertices (Fin 143) W midpoint → Nat,
      ConventionalGraceful (graftGraph (pathGraph 142) H midpoint root) (142+Q) f ∧
      f (graftEmbed midpoint root (selectedPoint d hd right))=0 := by
  obtain ⟨w,hw,hx⟩ := all_packets d hd right
  exact graft_extreme_conventional H root g Q hg hroot w hw
    (selectedPoint d hd right) hx

end GracefulBoundary.Rooted71
