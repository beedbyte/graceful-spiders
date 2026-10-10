import Positive
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open GracefulBoundary GracefulBoundary.Rooted71 Audit
example : Q24Rooted.ZeroAt singleton ⟨0,by decide⟩ 0 58 ⟨0,by decide⟩ := (K119Through118.interior singleton ⟨0,by decide⟩ singletonLabel 0 119 singletonGraceful rfl (by decide)).1
