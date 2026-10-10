import Positive
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open GracefulBoundary GracefulBoundary.Rooted71 Audit
example : TerminalNormalized.ActualAt singleton ⟨0,by decide⟩ 0 58 29 4 := (exact_family34 singleton ⟨0,by decide⟩ singletonLabel 0 0 25 (by decide) singletonGraceful rfl (by decide)).1
