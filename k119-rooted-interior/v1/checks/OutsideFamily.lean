import Positive
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open GracefulBoundary GracefulBoundary.Rooted71 Audit
example : TerminalNormalized.ActualAt singleton ⟨0,by decide⟩ 0 958 479 1 := (exact_family34 singleton ⟨0,by decide⟩ singletonLabel 0 2 478 (by decide) singletonGraceful rfl (by decide)).1
