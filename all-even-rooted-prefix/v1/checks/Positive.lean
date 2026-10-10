import ReplaySupport
open GracefulBoundary GracefulBoundary.Rooted71 GracefulBoundary.EvenRootedPrefix

theorem expanded_universal {W F : Type} (H : IndexedGraph W F) (r : W)
    (g : W → Nat) (Q K d : Nat) (hg : ConventionalGraceful H Q g)
    (hr : g r=0) (hK : 20≤K) (heven : K%2=0)
    (hd : 2≤d ∧ d≤GapFill.depthPrefix K) :
    (∃ f : GraftVertices (Fin (2*K+1)) W (center K) → Nat,
      ConventionalGraceful (graftGraph (pathGraph (2*K)) H (center K) r) (2*K+Q) f ∧
      f (graftEmbed (center K) r ⟨K-d,by have := GapFill.prefix_inside K (by omega); omega⟩)=0) ∧
    (∃ f : GraftVertices (Fin (2*K+1)) W (center K) → Nat,
      ConventionalGraceful (graftGraph (pathGraph (2*K)) H (center K) r) (2*K+Q) f ∧
      f (graftEmbed (center K) r ⟨K+d,by have := GapFill.prefix_inside K (by omega); omega⟩)=0) := by
  exact all_even_prefix H r g Q K d hg hr hK heven hd

set_option pp.all false in
#print expanded_universal
#print GracefulBoundary.EvenRootedPrefix.all_even_prefix

theorem triangle_K20_d2_left :
    ∃ f : GraftVertices (Fin 41) (Fin 3) (center 20) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 40) Replay.triangle (center 20) ⟨0,by decide⟩) 43 f ∧
      f (graftEmbed (center 20) ⟨0,by decide⟩ (⟨18,by decide⟩ : Fin 41))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 20 2
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).1

theorem triangle_K20_d2_right :
    ∃ f : GraftVertices (Fin 41) (Fin 3) (center 20) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 40) Replay.triangle (center 20) ⟨0,by decide⟩) 43 f ∧
      f (graftEmbed (center 20) ⟨0,by decide⟩ (⟨22,by decide⟩ : Fin 41))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 20 2
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).2

theorem triangle_K20_d11_left :
    ∃ f : GraftVertices (Fin 41) (Fin 3) (center 20) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 40) Replay.triangle (center 20) ⟨0,by decide⟩) 43 f ∧
      f (graftEmbed (center 20) ⟨0,by decide⟩ (⟨9,by decide⟩ : Fin 41))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 20 11
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).1

theorem triangle_K20_d11_right :
    ∃ f : GraftVertices (Fin 41) (Fin 3) (center 20) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 40) Replay.triangle (center 20) ⟨0,by decide⟩) 43 f ∧
      f (graftEmbed (center 20) ⟨0,by decide⟩ (⟨31,by decide⟩ : Fin 41))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 20 11
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).2

theorem triangle_K36_d2_left :
    ∃ f : GraftVertices (Fin 73) (Fin 3) (center 36) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 72) Replay.triangle (center 36) ⟨0,by decide⟩) 75 f ∧
      f (graftEmbed (center 36) ⟨0,by decide⟩ (⟨34,by decide⟩ : Fin 73))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 36 2
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).1

theorem triangle_K36_d2_right :
    ∃ f : GraftVertices (Fin 73) (Fin 3) (center 36) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 72) Replay.triangle (center 36) ⟨0,by decide⟩) 75 f ∧
      f (graftEmbed (center 36) ⟨0,by decide⟩ (⟨38,by decide⟩ : Fin 73))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 36 2
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).2

theorem triangle_K36_d27_left :
    ∃ f : GraftVertices (Fin 73) (Fin 3) (center 36) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 72) Replay.triangle (center 36) ⟨0,by decide⟩) 75 f ∧
      f (graftEmbed (center 36) ⟨0,by decide⟩ (⟨9,by decide⟩ : Fin 73))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 36 27
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).1

theorem triangle_K36_d27_right :
    ∃ f : GraftVertices (Fin 73) (Fin 3) (center 36) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 72) Replay.triangle (center 36) ⟨0,by decide⟩) 75 f ∧
      f (graftEmbed (center 36) ⟨0,by decide⟩ (⟨63,by decide⟩ : Fin 73))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 36 27
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).2

theorem triangle_K124_d2_left :
    ∃ f : GraftVertices (Fin 249) (Fin 3) (center 124) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 248) Replay.triangle (center 124) ⟨0,by decide⟩) 251 f ∧
      f (graftEmbed (center 124) ⟨0,by decide⟩ (⟨122,by decide⟩ : Fin 249))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 124 2
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).1

theorem triangle_K124_d2_right :
    ∃ f : GraftVertices (Fin 249) (Fin 3) (center 124) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 248) Replay.triangle (center 124) ⟨0,by decide⟩) 251 f ∧
      f (graftEmbed (center 124) ⟨0,by decide⟩ (⟨126,by decide⟩ : Fin 249))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 124 2
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).2

theorem triangle_K124_d89_left :
    ∃ f : GraftVertices (Fin 249) (Fin 3) (center 124) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 248) Replay.triangle (center 124) ⟨0,by decide⟩) 251 f ∧
      f (graftEmbed (center 124) ⟨0,by decide⟩ (⟨35,by decide⟩ : Fin 249))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 124 89
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).1

theorem triangle_K124_d89_right :
    ∃ f : GraftVertices (Fin 249) (Fin 3) (center 124) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 248) Replay.triangle (center 124) ⟨0,by decide⟩) 251 f ∧
      f (graftEmbed (center 124) ⟨0,by decide⟩ (⟨213,by decide⟩ : Fin 249))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 124 89
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).2

theorem triangle_K126_d2_left :
    ∃ f : GraftVertices (Fin 253) (Fin 3) (center 126) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 252) Replay.triangle (center 126) ⟨0,by decide⟩) 255 f ∧
      f (graftEmbed (center 126) ⟨0,by decide⟩ (⟨124,by decide⟩ : Fin 253))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 126 2
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).1

theorem triangle_K126_d2_right :
    ∃ f : GraftVertices (Fin 253) (Fin 3) (center 126) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 252) Replay.triangle (center 126) ⟨0,by decide⟩) 255 f ∧
      f (graftEmbed (center 126) ⟨0,by decide⟩ (⟨128,by decide⟩ : Fin 253))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 126 2
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).2

theorem triangle_K126_d107_left :
    ∃ f : GraftVertices (Fin 253) (Fin 3) (center 126) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 252) Replay.triangle (center 126) ⟨0,by decide⟩) 255 f ∧
      f (graftEmbed (center 126) ⟨0,by decide⟩ (⟨19,by decide⟩ : Fin 253))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 126 107
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).1

theorem triangle_K126_d107_right :
    ∃ f : GraftVertices (Fin 253) (Fin 3) (center 126) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 252) Replay.triangle (center 126) ⟨0,by decide⟩) 255 f ∧
      f (graftEmbed (center 126) ⟨0,by decide⟩ (⟨233,by decide⟩ : Fin 253))=0 := by
  exact (all_even_prefix Replay.triangle ⟨0,by decide⟩ Replay.lab 3 126 107
    Replay.conventional (by decide) (by decide) (by decide) (by decide)).2

set_option maxHeartbeats 20000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut checked : Nat := 0
  for (n,c) in env.constants.toList do
    if c.isTheorem && (n.toString.startsWith "GracefulBoundary." || n.toString.startsWith "Replay." || n.toString.startsWith "triangle_K" || n == `expanded_universal) then
      let ax ← Lean.collectAxioms n
      for a in ax do
        unless a == `propext || a == `Classical.choice || a == `Quot.sound do
          throwError "NONSTANDARD AXIOM {n}: {a}"
      checked := checked+1
      Lean.logInfo m!"AXIOMS_OK {n}: {ax}"
  Lean.logInfo m!"CLOSURES_CHECKED {checked}"
