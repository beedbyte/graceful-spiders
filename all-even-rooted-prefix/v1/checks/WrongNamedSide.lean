import ReplaySupport
open GracefulBoundary GracefulBoundary.Rooted71 GracefulBoundary.EvenRootedPrefix
example : ∃ f : GraftVertices (Fin 41) (Fin 3) (center 20) → Nat,
    ConventionalGraceful (graftGraph (pathGraph 40) Replay.triangle (center 20) ⟨0,by decide⟩) 43 f ∧
    f (graftEmbed (center 20) ⟨0,by decide⟩ (⟨22,by decide⟩ : Fin 41))=0 := by
  obtain ⟨f,hf,hz⟩ := (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 20 2
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).1
  exact ⟨f,hf,hz⟩
