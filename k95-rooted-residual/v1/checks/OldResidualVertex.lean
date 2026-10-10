import AuditPositive
open GracefulBoundary GracefulBoundary.Rooted71 ReplayAudit
example : ∃ f : GraftVertices (Fin 191) (Fin 3) (Q24Rooted.center 46) → Nat,
  ConventionalGraceful (graftGraph (pathGraph 190) triangle (Q24Rooted.center 46) ⟨0,by decide⟩) 193 f ∧
  f (.inr ⟨0,by decide⟩)=0 := (triangle_all_depths 1 (by decide)).1
