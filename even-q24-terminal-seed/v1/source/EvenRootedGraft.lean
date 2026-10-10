import EvenQ24

namespace GracefulBoundary.EvenRootedGraft

/-- Conventional vertex requirement: injective into the interval, without onto. -/
structure InjectiveBand {V : Type} (f : V → Nat) (lo hi : Nat) : Prop where
  bounds : ∀ v, lo≤f v ∧ f v≤hi
  injective : ∀ v w, f v=f w → v=w

/-- Ordinary graceful labeling for arbitrary finite graphs: full edge weights,
    injective vertex labels into the allowed interval. -/
structure ConventionalGraceful {V E : Type} (G : IndexedGraph V E)
    (M : Nat) (f : V → Nat) : Prop where
  vertices : InjectiveBand f 0 M
  edges : BandBijection (weight G f) 1 M

theorem conventional_of_graceful {V E : Type} (G : IndexedGraph V E)
    (M : Nat) (f : V → Nat) (hf : Graceful G M f) :
    ConventionalGraceful G M f :=
  ⟨⟨hf.vertices.bounds,hf.vertices.injective⟩,hf.edges⟩

theorem conventional_complement {V E : Type} (G : IndexedGraph V E)
    (M : Nat) (f : V → Nat) (hf : ConventionalGraceful G M f) :
    ConventionalGraceful G M (fun v => M-f v) := by
  constructor
  · constructor
    · intro v
      have hv := (hf.vertices.bounds v).2
      constructor <;> omega
    · intro v w he
      have hv := (hf.vertices.bounds v).2
      have hw := (hf.vertices.bounds w).2
      exact hf.vertices.injective v w (by omega)
  · have he : weight G (fun v => M-f v)=weight G f := by
      funext e
      exact complement_difference M _ _ (hf.vertices.bounds _).2 (hf.vertices.bounds _).2
    rw [he]
    exact hf.edges

theorem conventional_graft_vertices {V W : Type} (c : V) (d : W)
    (f : V → Nat) (g : W → Nat) (A M Q : Nat)
    (hf : BandBijection f 0 M) (hg : InjectiveBand g 0 Q)
    (hc : f c=A) (_hd : g d=0) :
    InjectiveBand (graftLabel c f g A Q) 0 (M+Q) := by
  have hAM : A≤M := hc ▸ (hf.bounds c).2
  constructor
  · intro v
    cases v with
    | inl v =>
      have hb := (hf.bounds v.val).2
      simp only [graftLabel,alphaShift]
      split <;> omega
    | inr w =>
      have hb := (hg.bounds w).2
      simp only [graftLabel]
      omega
  · intro v w heq
    cases v with
    | inl v =>
      cases w with
      | inl w =>
        have he : f v.val=f w.val := alphaShift_injective A Q _ _ heq
        have hv := hf.injective _ _ he
        exact congrArg Sum.inl (Subtype.ext hv)
      | inr w =>
        have he := (mixed_label_collision A Q (f v.val) (g w) (hg.bounds w).2).mp heq
        have hv : v.val=c := hf.injective _ _ (he.1.trans hc.symm)
        exact False.elim (v.property hv)
    | inr v =>
      cases w with
      | inl w =>
        have he := (mixed_label_collision A Q (f w.val) (g v) (hg.bounds v).2).mp heq.symm
        have hw : w.val=c := hf.injective _ _ (he.1.trans hc.symm)
        exact False.elim (w.property hw)
      | inr w =>
        have he : g v=g w := by simpa only [graftLabel,Nat.add_left_cancel_iff] using heq
        exact congrArg Sum.inr (hg.injective _ _ he)

theorem conventional_graft {V W E F : Type} (G : IndexedGraph V E)
    (H : IndexedGraph W F) (c : V) (d : W) (f : V → Nat) (g : W → Nat)
    (A M Q : Nat) (hf : Graceful G M f) (hg : ConventionalGraceful H Q g)
    (hc : f c=A) (hd : g d=0) (cut : Alpha G A f) :
    ConventionalGraceful (graftGraph G H c d) (M+Q) (graftLabel c f g A Q) := by
  refine ⟨conventional_graft_vertices c d f g A M Q hf.vertices hg.vertices hc hd,?_⟩
  constructor
  · intro e
    cases e with
    | inl e =>
      rw [graft_weight_left G H c d f g A Q hc hd cut]
      have he := hf.edges.bounds e
      omega
    | inr e =>
      rw [graft_weight_right]
      have he := hg.edges.bounds e
      omega
  · intro e e' heq
    cases e with
    | inl e =>
      cases e' with
      | inl e' =>
        rw [graft_weight_left G H c d f g A Q hc hd cut,
          graft_weight_left G H c d f g A Q hc hd cut] at heq
        exact congrArg Sum.inl (hf.edges.injective e e' (by omega))
      | inr e' =>
        rw [graft_weight_left G H c d f g A Q hc hd cut,graft_weight_right] at heq
        have h1 := hf.edges.bounds e
        have h2 := hg.edges.bounds e'
        omega
    | inr e =>
      cases e' with
      | inl e' =>
        rw [graft_weight_right,graft_weight_left G H c d f g A Q hc hd cut] at heq
        have h1 := hg.edges.bounds e
        have h2 := hf.edges.bounds e'
        omega
      | inr e' =>
        rw [graft_weight_right,graft_weight_right] at heq
        exact congrArg Sum.inr (hg.edges.injective e e' heq)
  · intro x hx htop
    by_cases hq : x≤Q
    · obtain ⟨e,he⟩ := hg.edges.onto x hx hq
      exact ⟨.inr e,by rw [graft_weight_right,he]⟩
    · obtain ⟨e,he⟩ := hf.edges.onto (x-Q) (by omega) (by omega)
      exact ⟨.inl e,by rw [graft_weight_left G H c d f g A Q hc hd cut,he]; omega⟩


end GracefulBoundary.EvenRootedGraft
