import StateEight
namespace GracefulBoundary.FixedEven

structure MaximumAnchor {V E : Type} (G : IndexedGraph V E) (root z o : V) (ce ze : E) : Prop where
  root_edge_source : G.source ce=root
  root_edge_target : G.target ce=z
  zero_edge_source : G.source ze=z
  zero_edge_target : G.target ze=o
  incident : ∀e,e=ce ∨ e=ze ∨ (G.source e≠z ∧ G.target e≠z)

def leavesGraph {V E : Type} (G : IndexedGraph V E) (root : V) (m : Nat) : IndexedGraph (Sum V (Fin m)) (Sum E (Fin m)) where
  source := fun e => match e with | .inl e => .inl (G.source e) | .inr _ => .inl root
  target := fun e => match e with | .inl e => .inl (G.target e) | .inr j => .inr j

theorem lifted_label {V E : Type} (G : IndexedGraph V E) (q m : Nat) (g : V → Nat)
    (hg : Graceful G q g) (z : V) (hz : g z=q) (v : V) (hv : v≠z) :
    CenterLeaves.insertLabel g q m (.inl v)=g v := by
  have bound := (hg.vertices.bounds v).2
  have neq : g v≠q := by intro he; exact hv (hg.vertices.injective v z (he.trans hz.symm))
  dsimp only [CenterLeaves.insertLabel]
  rw [ite_eq_right (by omega)]

theorem maximum_incident_weights {V E : Type} (G : IndexedGraph V E) (q : Nat) (g : V → Nat)
    (root z o : V) (ce ze : E) (ha : MaximumAnchor G root z o ce ze)
    (hr : g root=1) (hz : g z=q) (ho : g o=0) (hq : 2≤q) :
    weight G g ce=q-1 ∧ weight G g ze=q := by
  dsimp only [weight]
  rw [ha.root_edge_source,ha.root_edge_target,ha.zero_edge_source,ha.zero_edge_target,hr,hz,ho]
  dsimp only [distance]
  constructor <;> omega

theorem maximum_leaf_old_weights {V E : Type} (G : IndexedGraph V E) (q m : Nat) (g : V → Nat)
    (hg : Graceful G q g) (root z o : V) (ce ze : E) (ha : MaximumAnchor G root z o ce ze)
    (hr : g root=1) (hz : g z=q) (ho : g o=0) (hq : 2≤q) (e : E) :
    weight (leavesGraph G root m) (CenterLeaves.insertLabel g q m) (.inl e)=
      CenterLeaves.insertLabel (weight G g) (q-1) m (.inl e) := by
  have pins := maximum_incident_weights G q g root z o ce ze ha hr hz ho hq
  have rootNe : root≠z := by intro he; have eq := congrArg g he; rw [hr,hz] at eq; omega
  have zeroNe : o≠z := by intro he; have eq := congrArg g he; rw [ho,hz] at eq; omega
  by_cases hc : e=ce
  · subst e
    dsimp only [weight,leavesGraph]
    rw [ha.root_edge_source,ha.root_edge_target,lifted_label G q m g hg z hz root rootNe]
    simp only [CenterLeaves.insertLabel,hz,hr,Nat.le_refl,ite_true,pins.1]
    dsimp only [distance]; omega
  · by_cases he : e=ze
    · subst e
      dsimp only [weight,leavesGraph]
      rw [ha.zero_edge_source,ha.zero_edge_target,lifted_label G q m g hg z hz o zeroNe]
      simp only [CenterLeaves.insertLabel,hz,ho,Nat.le_refl,ite_true,pins.2]
      rw [ite_eq_left (by omega)]
      dsimp only [distance]; omega
    · have far : G.source e≠z ∧ G.target e≠z := by rcases ha.incident e with h|h|h; contradiction; contradiction; exact h
      have bound := (hg.edges.bounds e).2
      have neqC : weight G g e≠q-1 := by intro h; exact hc (hg.edges.injective e ce (h.trans pins.1.symm))
      have neqZ : weight G g e≠q := by intro h; exact he (hg.edges.injective e ze (h.trans pins.2.symm))
      have small : weight G g e<q-1 := by omega
      dsimp only [weight,leavesGraph]
      rw [lifted_label G q m g hg z hz _ far.1,lifted_label G q m g hg z hz _ far.2]
      change weight G g e=CenterLeaves.insertLabel (weight G g) (q-1) m (.inl e)
      dsimp only [CenterLeaves.insertLabel]
      rw [ite_eq_right (by omega)]

/-- Arbitrary indexed graph with exactly the stated two maximum incidences. -/
theorem maximum_leaf_extension {V E : Type} (G : IndexedGraph V E) (q m : Nat) (g : V → Nat)
    (hg : Graceful G q g) (root z o : V) (ce ze : E) (ha : MaximumAnchor G root z o ce ze)
    (hr : g root=1) (hz : g z=q) (ho : g o=0) (hq : 2≤q) :
    Graceful (leavesGraph G root m) (q+m) (CenterLeaves.insertLabel g q m) ∧
      CenterLeaves.insertLabel g q m (.inl root)=1 := by
  have rootNe : root≠z := by intro he; have eq := congrArg g he; rw [hr,hz] at eq; omega
  constructor
  · constructor
    · exact CenterLeaves.band_insert g 0 q q m hg.vertices (by omega)
    · have hb := CenterLeaves.band_insert (weight G g) 1 q (q-1) m hg.edges (by omega)
      have eq : weight (leavesGraph G root m) (CenterLeaves.insertLabel g q m)=CenterLeaves.insertLabel (weight G g) (q-1) m := by
        funext e; cases e with
        | inl e => exact maximum_leaf_old_weights G q m g hg root z o ce ze ha hr hz ho hq e
        | inr j =>
          dsimp only [weight,leavesGraph]
          rw [lifted_label G q m g hg z hz root rootNe,hr]
          dsimp only [CenterLeaves.insertLabel,distance]; omega
      rw [eq]; exact hb
  · rw [lifted_label G q m g hg z hz root rootNe,hr]

end GracefulBoundary.FixedEven
