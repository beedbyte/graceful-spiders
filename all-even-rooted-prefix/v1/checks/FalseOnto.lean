import ReplaySupport
open GracefulBoundary GracefulBoundary.Rooted71 GracefulBoundary.EvenRootedPrefix
example : ∃ f : GraftVertices (Fin 41) (Fin 3) (center 20) → Nat,
    Graceful (graftGraph (pathGraph 40) Replay.triangle (center 20) ⟨0,by decide⟩) 43 f := by
  obtain ⟨f,hf,hz⟩ := (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 20 2
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).1
  exact ⟨f,hf⟩
