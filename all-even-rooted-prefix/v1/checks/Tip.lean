import ReplaySupport
open GracefulBoundary GracefulBoundary.Rooted71 GracefulBoundary.EvenRootedPrefix
example : True := by
  have h := all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 20 20
    Replay.conventional (by decide) (by decide) (by decide) (by decide)
  trivial
