import FixedBases
namespace GracefulBoundary.FixedEven

abbrev cuts (t x y : Nat) : Prop := (x≤t ∧ t<y) ∨ (y≤t ∧ t<x)
def shift (t k x : Nat) := if t<x then x+k else x
def label {V : Type} (g : V → Nat) (t k : Nat) (a : Fin k → Nat) : Sum V (Fin k) → Nat
  | .inl v => shift t k (g v)
  | .inr d => a d

def graph {V E : Type} (G : IndexedGraph V E) (root : V) (k : Nat) : IndexedGraph (Sum V (Fin k)) (Sum E (Fin k)) where
  source := fun e => match e with
    | .inl e => .inl (G.source e)
    | .inr d => if d.val=0 then .inl root else .inr ⟨d.val-1,by omega⟩
  target := fun e => match e with
    | .inl e => .inl (G.target e)
    | .inr d => .inr d

theorem shifted_distance (t k x y : Nat) :
    distance (shift t k x) (shift t k y)=if cuts t x y then distance x y+k else distance x y := by
  dsimp only [shift,cuts,distance]
  repeat (any_goals (first | omega | split))

theorem gap_label_bijection {V : Type} (g : V → Nat) (q t k : Nat)
    (hg : BandBijection g 0 q) (ht : t≤q) (a : Fin k → Nat)
    (ha : BandBijection a (t+1) (t+k)) : BandBijection (label g t k a) 0 (q+k) := by
  constructor
  · intro v; cases v with
    | inl v => have := hg.bounds v; dsimp only [label,shift]; split <;> omega
    | inr d => have := ha.bounds d; dsimp only [label]; omega
  · intro v w he; cases v with
    | inl v => cases w with
      | inl w =>
        have eq : g v=g w := by dsimp only [label,shift] at he; repeat (any_goals (first | omega | split at he))
        exact congrArg Sum.inl (hg.injective _ _ eq)
      | inr d => have := ha.bounds d; dsimp only [label,shift] at he; split at he <;> omega
    | inr d => cases w with
      | inl w => have := ha.bounds d; dsimp only [label,shift] at he; split at he <;> omega
      | inr e => exact congrArg Sum.inr (ha.injective _ _ he)
  · intro x hx hq
    by_cases low : x≤t
    · obtain ⟨v,hv⟩ := hg.onto x hx (by omega)
      refine ⟨.inl v,?_⟩; dsimp only [label,shift]; rw [hv,ite_eq_right (by omega)]
    · by_cases middle : x≤t+k
      · obtain ⟨d,hd⟩ := ha.onto x (by omega) middle; exact ⟨.inr d,hd⟩
      · obtain ⟨v,hv⟩ := hg.onto (x-k) (by omega) (by omega)
        refine ⟨.inl v,?_⟩; dsimp only [label,shift]; rw [hv,ite_eq_left (by omega)]; omega

structure ArmWeights (k B : Nat) (w : Fin k → Nat) : Prop where
  injective : ∀d e,w d=w e → d=e
  shape : ∀d,w d=B ∨ (1≤w d ∧ w d<k)
  bridge : ∃d,w d=B
  internal : ∀x,1≤x → x<k → ∃d,w d=x

def code (k B : Nat) (w : Fin k → Nat) (hw : ArmWeights k B w) (hk : 1≤k) (d : Fin k) : Fin k :=
  ⟨if w d=B then 0 else w d,by have := hw.shape d; split <;> omega⟩

theorem code_injective (k B : Nat) (w : Fin k → Nat) (hw : ArmWeights k B w) (hk : 1≤k) :
    ∀d e,code k B w hw hk d=code k B w hw hk e → d=e := by
  intro d e he
  have hv := congrArg Fin.val he
  have hd := hw.shape d; have he := hw.shape e
  have eq : w d=w e := by dsimp only [code] at hv; repeat (any_goals (first | omega | split at hv))
  exact hw.injective _ _ eq

theorem code_onto (k B : Nat) (w : Fin k → Nat) (hw : ArmWeights k B w) (hk : 1≤k) (hB : k≤B) :
    ∀i:Fin k,∃d,code k B w hw hk d=i := by
  intro i
  by_cases hi : i.val=0
  · obtain ⟨d,hd⟩ := hw.bridge
    exact ⟨d,by apply Fin.ext; dsimp only [code]; rw [hd,ite_eq_left rfl]; exact hi.symm⟩
  · obtain ⟨d,hd⟩ := hw.internal i.val (by omega) i.isLt
    exact ⟨d,by apply Fin.ext; dsimp only [code]; rw [hd,ite_eq_right (by have := i.isLt; omega)]⟩

noncomputable def inverseCode (k B : Nat) (w : Fin k → Nat) (hw : ArmWeights k B w) (hk : 1≤k) (hB : k≤B) (i : Fin k) : Fin k :=
  Classical.choose (code_onto k B w hw hk hB i)

theorem code_right_inverse (k B : Nat) (w : Fin k → Nat) (hw : ArmWeights k B w) (hk : 1≤k) (hB : k≤B) (i : Fin k) :
    code k B w hw hk (inverseCode k B w hw hk hB i)=i := Classical.choose_spec (code_onto k B w hw hk hB i)

theorem code_left_inverse (k B : Nat) (w : Fin k → Nat) (hw : ArmWeights k B w) (hk : 1≤k) (hB : k≤B) (d : Fin k) :
    inverseCode k B w hw hk hB (code k B w hw hk d)=d :=
  code_injective k B w hw hk _ _ (code_right_inverse k B w hw hk hB _)

theorem code_weight (k B : Nat) (w : Fin k → Nat) (hw : ArmWeights k B w) (hk : 1≤k) (hB : k≤B) (d : Fin k) :
    (if (code k B w hw hk d).val=0 then B else (code k B w hw hk d).val)=w d := by
  dsimp only [code]
  have hd := hw.shape d
  repeat (any_goals (first | omega | split))

theorem custom_gap_weights {E : Type} (w : E → Nat) (q k B : Nat) (hw : BandBijection w 1 q)
    (hk : 1≤k) (hB : k≤B ∧ B≤q) (hm : B%k=0) (a : Fin k → Nat) (ha : ArmWeights k B a) :
    BandBijection (fun e : Sum E (Fin k) => match e with | .inl e => gapWeight k B (w e) | .inr d => a d) 1 (q+k) := by
  let f : Sum E (Fin k) → Sum E (Fin k) := fun e => match e with | .inl e => .inl e | .inr d => .inr (code k B a ha hk d)
  let fi : Sum E (Fin k) → Sum E (Fin k) := fun e => match e with | .inl e => .inl e | .inr d => .inr (inverseCode k B a ha hk hB.1 d)
  have hl : ∀e,fi (f e)=e := by intro e; cases e with
    | inl e => rfl
    | inr d => dsimp only [f,fi]; rw [code_left_inverse]
  have hr : ∀e,f (fi e)=e := by intro e; cases e with
    | inl e => rfl
    | inr d => dsimp only [f,fi]; rw [code_right_inverse]
  have hb := NearTip.band_transport (gapWeights w k B) 1 (q+k) (gap_weight_bijection w q k B hw hk hB hm) f fi hl hr
  have eq : (fun e => gapWeights w k B (f e))=(fun e : Sum E (Fin k) => match e with | .inl e => gapWeight k B (w e) | .inr d => a d) := by
    funext e; cases e with
    | inl e => rfl
    | inr d => exact code_weight k B a ha hk hB.1 d
  rw [eq] at hb; exact hb

/-- Complete actual graph graft under an exact old crossing and new arm-weight contract. -/
theorem gap_graft {V E : Type} (G : IndexedGraph V E) (root : V) (g : V → Nat) (q k t B : Nat)
    (hg : Graceful G q g) (hk : 1≤k) (ht : t≤q) (hB : k≤B ∧ B≤q) (hm : B%k=0)
    (crossing : ∀e,cuts t (g (G.source e)) (g (G.target e)) ↔ gains k B (weight G g e))
    (a : Fin k → Nat) (ha : BandBijection a (t+1) (t+k))
    (hwa : ArmWeights k B (fun d => weight (graph G root k) (label g t k a) (.inr d))) :
    Graceful (graph G root k) (q+k) (label g t k a) := by
  constructor
  · exact gap_label_bijection g q t k hg.vertices ht a ha
  · have hb := custom_gap_weights (weight G g) q k B hg.edges hk hB hm _ hwa
    have eq : weight (graph G root k) (label g t k a)=
        (fun e : Sum E (Fin k) => match e with | .inl e => gapWeight k B (weight G g e) | .inr d => weight (graph G root k) (label g t k a) (.inr d)) := by
      funext e; cases e with
      | inl e =>
        dsimp only [weight,graph,label]
        rw [shifted_distance]
        change (if cuts t (g (G.source e)) (g (G.target e)) then weight G g e+k else weight G g e)=gapWeight k B (weight G g e)
        simp only [gapWeight,←crossing e]
      | inr d => rfl
    rw [eq]; exact hb

end GracefulBoundary.FixedEven
