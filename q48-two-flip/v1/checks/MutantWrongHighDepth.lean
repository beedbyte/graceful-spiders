import Q48Family
open GracefulBoundary
open GracefulBoundary.Q48Flip
set_option maxHeartbeats 0
set_option maxRecDepth 16384
example : ∃ f : SpiderVertex 2 0 71 → Nat, Graceful (spiderGraph 2 0 71) (2*71+0) f ∧ f (.arm ⟨0,by decide⟩ ⟨65,by decide⟩)=0 := (terminal_actual 0 2 0 (by decide) ⟨0,by decide⟩).2
