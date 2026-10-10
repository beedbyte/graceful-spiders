import TerminalSeed56
import K119Rooted

namespace GracefulBoundary.K119Through114
open Rooted71

/-- Separate prescribed zeros on both named arms, for all depths1 through114. -/
theorem interior {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hd : 1≤d ∧ d≤114) :
    Q24Rooted.ZeroAt H root Q 58 ⟨119-d,by omega⟩ ∧
    Q24Rooted.ZeroAt H root Q 58 ⟨119+d,by omega⟩ := by
  by_cases hold : d≤110
  · exact K119Rooted.interior H root g Q d hg hroot ⟨hd.1,hold⟩
  by_cases h12 : d≤112
  · have h : d=111 ∨ d=112 := by omega
    exact TerminalNormalized.rooted_both H root g Q 1 d (by decide) hg hroot h
  · have h : d=113 ∨ d=114 := by omega
    exact TerminalSeed56.rooted_both H root g Q 1 d (by decide) hg hroot h

/-- The full arbitrary-H graph type and the two physical target indices. -/
theorem expanded {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hd : 1≤d ∧ d≤114) :
    (∃ f : GraftVertices (Fin 239) W (⟨119,by decide⟩ : Fin 239) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 238) H (⟨119,by decide⟩ : Fin 239) root)
        (238+Q) f ∧
      f (graftEmbed (⟨119,by decide⟩ : Fin 239) root ⟨119-d,by omega⟩)=0) ∧
    (∃ f : GraftVertices (Fin 239) W (⟨119,by decide⟩ : Fin 239) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 238) H (⟨119,by decide⟩ : Fin 239) root)
        (238+Q) f ∧
      f (graftEmbed (⟨119,by decide⟩ : Fin 239) root ⟨119+d,by omega⟩)=0) :=
  interior H root g Q d hg hroot hd

end GracefulBoundary.K119Through114
