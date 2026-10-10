import Boundary
namespace GracefulBoundary

structure BandBijection {V : Type} (f : V → Nat) (lo hi : Nat) : Prop where
  bounds : ∀ v, lo ≤ f v ∧ f v ≤ hi
  injective : ∀ v w, f v = f w → v=w
  onto : ∀ x, lo ≤ x → x ≤ hi → ∃ v, f v=x

structure IndexedGraph (V E : Type) where
  source : E → V
  target : E → V

def weight {V E : Type} (G : IndexedGraph V E) (f : V → Nat) (e : E) : Nat :=
  distance (f (G.source e)) (f (G.target e))

structure Graceful {V E : Type} (G : IndexedGraph V E) (M : Nat) (f : V → Nat) : Prop where
  vertices : BandBijection f 0 M
  edges : BandBijection (weight G f) 1 M

def Alpha {V E : Type} (G : IndexedGraph V E) (A : Nat) (f : V → Nat) : Prop :=
  ∀ e, (f (G.source e) ≤ A ∧ A < f (G.target e)) ∨
        (f (G.target e) ≤ A ∧ A < f (G.source e))

abbrev GraftVertices (V W : Type) (c : V) := Sum {v : V // v ≠ c} W

noncomputable def graftEmbed {V W : Type} (c : V) (d : W) (v : V) : GraftVertices V W c := by
  classical
  exact if h : v=c then Sum.inr d else Sum.inl ⟨v,h⟩

def graftLabel {V W : Type} (c : V) (f : V → Nat) (g : W → Nat) (A Q : Nat) :
    GraftVertices V W c → Nat
  | .inl v => alphaShift A Q (f v.val)
  | .inr w => A + g w

noncomputable def graftGraph {V W E F : Type} (G : IndexedGraph V E)
    (H : IndexedGraph W F) (c : V) (d : W) : IndexedGraph (GraftVertices V W c) (Sum E F) where
  source := fun e => match e with
    | .inl a => graftEmbed c d (G.source a)
    | .inr b => .inr (H.source b)
  target := fun e => match e with
    | .inl a => graftEmbed c d (G.target a)
    | .inr b => .inr (H.target b)

theorem graftLabel_embed {V W : Type} (c : V) (d : W) (f : V → Nat) (g : W → Nat)
    (A Q : Nat) (hc : f c=A) (hd : g d=0) (v : V) :
    graftLabel c f g A Q (graftEmbed c d v) = alphaShift A Q (f v) := by
  classical
  by_cases h : v=c
  · subst v; simp [graftEmbed, graftLabel, hc, hd, alphaShift]
  · simp [graftEmbed, h, graftLabel]

theorem graft_vertices {V W : Type} (c : V) (d : W) (f : V → Nat) (g : W → Nat)
    (A M Q : Nat) (hf : BandBijection f 0 M) (hg : BandBijection g 0 Q)
    (hc : f c=A) (_hd : g d=0) : BandBijection (graftLabel c f g A Q) 0 (M+Q) := by
  have hAM : A ≤ M := hc ▸ (hf.bounds c).2
  constructor
  · intro v
    cases v with
    | inl v =>
      have hb := (hf.bounds v.val).2
      simp only [graftLabel, alphaShift]
      split <;> omega
    | inr w => have hb := (hg.bounds w).2; simp only [graftLabel]; omega
  · intro v w heq
    cases v with
    | inl v =>
      cases w with
      | inl w =>
        have he : f v.val = f w.val := alphaShift_injective A Q _ _ heq
        have hv := hf.injective _ _ he
        have hs : v=w := Subtype.ext hv
        exact congrArg Sum.inl hs
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
        have he : g v=g w := by simpa only [graftLabel, Nat.add_left_cancel_iff] using heq
        exact congrArg Sum.inr (hg.injective _ _ he)
  · intro x _ hx
    rcases amalgam_label_coverage A M Q x hAM hx with ⟨b, hb, he⟩ | ⟨y, hy, hne, he⟩
    · obtain ⟨w, hw⟩ := hg.onto b (by omega) hb
      exact ⟨.inr w, by simp [graftLabel, hw, he]⟩
    · obtain ⟨v, hv⟩ := hf.onto y (by omega) hy
      have hvc : v ≠ c := by intro h; subst v; exact hne (hv.symm.trans hc)
      exact ⟨.inl ⟨v,hvc⟩, by simp [graftLabel, hv, he]⟩

theorem distance_comm (x y : Nat) : distance x y = distance y x := by unfold distance; omega

theorem alphaShift_edge (A Q x y : Nat)
    (h : (x ≤ A ∧ A < y) ∨ (y ≤ A ∧ A < x)) :
    distance (alphaShift A Q x) (alphaShift A Q y) = distance x y + Q := by
  rcases h with h | h
  · rw [distance_comm, alphaShift_crossing A Q x y h.1 h.2, distance_comm x y]
  · exact alphaShift_crossing A Q y x h.1 h.2

theorem graft_weight_left {V W E F : Type} (G : IndexedGraph V E) (H : IndexedGraph W F)
    (c : V) (d : W) (f : V → Nat) (g : W → Nat) (A Q : Nat)
    (hc : f c=A) (hd : g d=0) (cut : Alpha G A f) (e : E) :
    weight (graftGraph G H c d) (graftLabel c f g A Q) (.inl e) = weight G f e+Q := by
  change distance (graftLabel c f g A Q (graftEmbed c d (G.source e)))
    (graftLabel c f g A Q (graftEmbed c d (G.target e))) = _
  rw [graftLabel_embed c d f g A Q hc hd, graftLabel_embed c d f g A Q hc hd]
  exact alphaShift_edge A Q _ _ (cut e)

theorem graft_weight_right {V W E F : Type} (G : IndexedGraph V E) (H : IndexedGraph W F)
    (c : V) (d : W) (f : V → Nat) (g : W → Nat) (A Q : Nat) (e : F) :
    weight (graftGraph G H c d) (graftLabel c f g A Q) (.inr e) = weight H g e := by
  exact translate_difference A _ _

/-- General graceful alpha amalgamation. Empty residual edge types are allowed.
    Both input graph labelings and the alpha crossing condition are hypotheses. -/
theorem graceful_graft {V W E F : Type} (G : IndexedGraph V E) (H : IndexedGraph W F)
    (c : V) (d : W) (f : V → Nat) (g : W → Nat) (A M Q : Nat)
    (hf : Graceful G M f) (hg : Graceful H Q g)
    (hc : f c=A) (hd : g d=0) (cut : Alpha G A f) :
    Graceful (graftGraph G H c d) (M+Q) (graftLabel c f g A Q) := by
  refine ⟨graft_vertices c d f g A M Q hf.vertices hg.vertices hc hd, ?_⟩
  constructor
  · intro e
    cases e with
    | inl e => rw [graft_weight_left G H c d f g A Q hc hd cut]; have he := hf.edges.bounds e; omega
    | inr e => rw [graft_weight_right]; have he := hg.edges.bounds e; omega
  · intro e e' heq
    cases e with
    | inl e =>
      cases e' with
      | inl e' =>
        rw [graft_weight_left G H c d f g A Q hc hd cut,
          graft_weight_left G H c d f g A Q hc hd cut] at heq
        exact congrArg Sum.inl (hf.edges.injective e e' (by omega))
      | inr e' =>
        rw [graft_weight_left G H c d f g A Q hc hd cut, graft_weight_right] at heq
        have h1 := hf.edges.bounds e; have h2 := hg.edges.bounds e'; omega
    | inr e =>
      cases e' with
      | inl e' =>
        rw [graft_weight_right, graft_weight_left G H c d f g A Q hc hd cut] at heq
        have h1 := hg.edges.bounds e; have h2 := hf.edges.bounds e'; omega
      | inr e' =>
        rw [graft_weight_right, graft_weight_right] at heq
        exact congrArg Sum.inr (hg.edges.injective e e' heq)
  · intro x hx htop
    by_cases hq : x ≤ Q
    · obtain ⟨e, he⟩ := hg.edges.onto x hx hq
      exact ⟨.inr e, by rw [graft_weight_right, he]⟩
    · obtain ⟨e, he⟩ := hf.edges.onto (x-Q) (by omega) (by omega)
      exact ⟨.inl e, by rw [graft_weight_left G H c d f g A Q hc hd cut, he]; omega⟩

end GracefulBoundary

