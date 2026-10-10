import Positive
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open GracefulBoundary GracefulBoundary.Rooted71 Audit
example : ∃ f : GraftVertices (Fin 239) (Fin 1) (Q24Rooted.center 58) → Nat,
 ConventionalGraceful (graftGraph (pathGraph 238) singleton (Q24Rooted.center 58) ⟨0,by decide⟩) 238 f ∧
 f (graftEmbed (Q24Rooted.center 58) ⟨0,by decide⟩ ⟨4,by decide⟩)=0 ∧
 f (graftEmbed (Q24Rooted.center 58) ⟨0,by decide⟩ ⟨234,by decide⟩)=0 :=
 K119Through118.interior singleton ⟨0,by decide⟩ singletonLabel 0 115 singletonGraceful rfl (by decide)
