import K119Through114
import TerminalSeed34
import TerminalSeed12

namespace GracefulBoundary.K119Through118
open Rooted71

/-- Separate prescribed zeros on both named arms, for all depths1 through118. -/
theorem interior {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hd : 1≤d ∧ d≤118) :
    Q24Rooted.ZeroAt H root Q 58 ⟨119-d,by omega⟩ ∧
    Q24Rooted.ZeroAt H root Q 58 ⟨119+d,by omega⟩ := by
  by_cases hold : d≤114
  · exact K119Through114.interior H root g Q d hg hroot ⟨hd.1,hold⟩
  by_cases h34 : d≤116
  · have h : d=115 ∨ d=116 := by omega
    exact TerminalSeed34.rooted_both H root g Q 1 d (by decide) hg hroot h
  · have h : d=117 ∨ d=118 := by omega
    exact TerminalSeed12.rooted_both H root g Q 1 d (by decide) hg hroot h

/-- The full arbitrary-H graph type and the two physical target indices. -/
theorem expanded {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hd : 1≤d ∧ d≤118) :
    (∃ f : GraftVertices (Fin 239) W (⟨119,by decide⟩ : Fin 239) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 238) H (⟨119,by decide⟩ : Fin 239) root)
        (238+Q) f ∧
      f (graftEmbed (⟨119,by decide⟩ : Fin 239) root ⟨119-d,by omega⟩)=0) ∧
    (∃ f : GraftVertices (Fin 239) W (⟨119,by decide⟩ : Fin 239) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 238) H (⟨119,by decide⟩ : Fin 239) root)
        (238+Q) f ∧
      f (graftEmbed (⟨119,by decide⟩ : Fin 239) root ⟨119+d,by omega⟩)=0) :=
  interior H root g Q d hg hroot hd

end GracefulBoundary.K119Through118
