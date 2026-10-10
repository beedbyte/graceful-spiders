import AuditPositive
open GracefulBoundary GracefulBoundary.Rooted71 ReplayAudit
example : ∃ f : GraftVertices (Fin 191) (Fin 3) (Q24Rooted.center 46) → Nat,
  Graceful (graftGraph (pathGraph 190) triangle (Q24Rooted.center 46) ⟨0,by decide⟩) 193 f ∧
  f (graftEmbed (Q24Rooted.center 46) ⟨0,by decide⟩ (⟨94,by decide⟩ : Fin 191))=0 :=
  (triangle_all_depths 1 (by decide)).1
