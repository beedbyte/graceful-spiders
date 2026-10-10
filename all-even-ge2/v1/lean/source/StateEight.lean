import AppendArm
namespace GracefulBoundary.FixedEven

@[simp] theorem fin_literal_val (n i : Nat) [NeZero n] : (@OfNat.ofNat (Fin n) i _).val=i%n := rfl

structure State8 (n : Nat) (hn : 2≤n) (g : SpiderVertex n 0 8 → Nat) : Prop where
  graceful : Graceful (spiderGraph n 0 8) (8*n) g
  root : g .center=1
  maximum : g (.arm ⟨1,by omega⟩ ⟨0,by omega⟩)=8*n
  zero : g (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)=0
  crossing : ∀e,cuts (cut8 n) (g ((spiderGraph n 0 8).source e)) (g ((spiderGraph n 0 8).target e)) ↔ gains 8 (bridge8 n) (weight (spiderGraph n 0 8) g e)

def emptySum {V : Type} (f : V → Nat) : Sum V (Fin 0) → Nat
  | .inl v => f v
  | .inr i => Fin.elim0 i

theorem empty_sum_band {V : Type} (f : V → Nat) (lo hi : Nat) (hf : BandBijection f lo hi) : BandBijection (emptySum f) lo hi := by
  constructor
  · intro v; cases v with
    | inl v => exact hf.bounds v
    | inr i => exact Fin.elim0 i
  · intro v w he; cases v with
    | inl v => cases w with
      | inl w => exact congrArg Sum.inl (hf.injective _ _ he)
      | inr i => exact Fin.elim0 i
    | inr i => exact Fin.elim0 i
  · intro x hx ht; obtain ⟨v,hv⟩ := hf.onto x hx ht; exact ⟨.inl v,hv⟩

@[simp] theorem fin17_val3 : (3:Fin 17).val=3 := rfl
@[simp] theorem fin17_val4 : (4:Fin 17).val=4 := rfl
@[simp] theorem fin17_val5 : (5:Fin 17).val=5 := rfl
@[simp] theorem fin17_val6 : (6:Fin 17).val=6 := rfl
@[simp] theorem fin17_val7 : (7:Fin 17).val=7 := rfl
@[simp] theorem fin17_val8 : (8:Fin 17).val=8 := rfl
@[simp] theorem fin17_val9 : (9:Fin 17).val=9 := rfl
@[simp] theorem fin17_val10 : (10:Fin 17).val=10 := rfl
@[simp] theorem fin17_val11 : (11:Fin 17).val=11 := rfl
@[simp] theorem fin17_val12 : (12:Fin 17).val=12 := rfl
@[simp] theorem fin17_val13 : (13:Fin 17).val=13 := rfl
@[simp] theorem fin17_val14 : (14:Fin 17).val=14 := rfl
@[simp] theorem fin17_val15 : (15:Fin 17).val=15 := rfl
@[simp] theorem fin17_val16 : (16:Fin 17).val=16 := rfl

def base8 (v : SpiderVertex 2 0 8) := emptySum (pathLabel 16 seed8) (CenterLeaves.Residual.toV 8 0 v)

theorem base8_graceful : Graceful (spiderGraph 2 0 8) 16 base8 := by
  have hc := seed8_valid
  have hp := list_path_graceful 16 seed8 hc.2.2.2.1 hc.2.2.2.2.1
  have hg : Graceful (CenterLeaves.graph 8 0) 16 (emptySum (pathLabel 16 seed8)) := by
    constructor
    · exact empty_sum_band _ 0 16 hp.vertices
    · have hb := empty_sum_band (weight (pathGraph 16) (pathLabel 16 seed8)) 1 16 hp.edges
      have eq : weight (CenterLeaves.graph 8 0) (emptySum (pathLabel 16 seed8))=emptySum (weight (pathGraph 16) (pathLabel 16 seed8)) := by
        funext e; cases e with
        | inl e => rfl
        | inr i => exact Fin.elim0 i
      rw [eq]; exact hb
  exact CenterLeaves.Residual.graceful_actual 8 0 _ hg

theorem base8_alpha : Alpha (spiderGraph 2 0 8) 8 base8 := by
  intro e; cases e with
  | leaf i => exact Fin.elim0 i
  | arm i d =>
    have hi : i.val=0 ∨ i.val=1 := by omega
    have hd : d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 ∨ d.val=4 ∨ d.val=5 ∨ d.val=6 ∨ d.val=7 := by omega
    rcases hi with hi|hi <;> rcases hd with hd|hd|hd|hd|hd|hd|hd|hd <;>
      simp only [spiderGraph] <;> simp only [hd,ite_true] <;>
      simp_all [base8,emptySum,CenterLeaves.Residual.toV,pathLabel,seed8] <;>
      (try dsimp) <;> (try simp) <;> omega

theorem base8_state : State8 2 (by omega) base8 := by
  constructor
  · exact base8_graceful
  · rfl
  · rfl
  · rfl
  · intro e
    have ha := base8_alpha e
    have hb := base8_graceful.edges.bounds e
    have hgain : gains 8 8 (weight (spiderGraph 2 0 8) base8 e) := by
      dsimp only [gains]
      by_cases hw : weight (spiderGraph 2 0 8) base8 e<8
      · have hm := Nat.mod_eq_of_lt hw; rw [hm]; omega
      · omega
    exact ⟨fun _ => hgain,fun _ => ha⟩

def next8 (n : Nat) (g : SpiderVertex n 0 8 → Nat) (v : SpiderVertex (n+1) 0 8) :=
  label g (cut8 n) 8 (arm8 n) (Append.toV n 0 8 v)

theorem state8_step (n : Nat) (hn : 2≤n) (g : SpiderVertex n 0 8 → Nat) (hg : State8 n hn g) :
    State8 (n+1) (by omega) (next8 n g) := by
  constructor
  · exact Append.graceful_actual n 0 8 (8*(n+1)) _ (step8_graceful (spiderGraph n 0 8) .center g n hn hg.graceful hg.root hg.crossing)
  · dsimp only [next8,Append.toV,label,shift]
    rw [hg.root,ite_eq_right (by dsimp only [cut8]; omega)]
  · dsimp only [next8,Append.toV]
    rw [dite_eq_left (by omega)]
    dsimp only [label,shift]
    rw [hg.maximum,ite_eq_left (by dsimp only [cut8]; omega)]
    omega
  · dsimp only [next8,Append.toV]
    rw [dite_eq_left (by omega)]
    dsimp only [label,shift]
    rw [hg.zero,ite_eq_right (by omega)]
  · intro e
    have hc := step8_crossing (spiderGraph n 0 8) .center g n hn hg.root hg.crossing (Append.toE n 0 8 e)
    rw [←Append.source_eq,←Append.target_eq,←Append.weights] at hc
    exact hc

theorem all_center_one_eight_residuals : ∀(n : Nat) (hn : 2≤n),∃g,State8 n hn g := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases base : n=2
    · subst n; exact ⟨base8,base8_state⟩
    · obtain ⟨j,rfl⟩ : ∃j,n=j+1 := ⟨n-1,by omega⟩
      obtain ⟨g,hg⟩ := ih j (by omega) (by omega)
      exact ⟨next8 j g,state8_step j (by omega) g hg⟩

/-- The same unbounded graph induction from any explicitly supplied k=8 base state. -/
theorem all_eight_residuals_from_supplied_base (g0 : SpiderVertex 2 0 8 → Nat)
    (hbase : State8 2 (by omega) g0) : ∀(n : Nat) (hn : 2≤n),∃g,State8 n hn g := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases base : n=2
    · subst n; exact ⟨g0,hbase⟩
    · obtain ⟨j,rfl⟩ : ∃j,n=j+1 := ⟨n-1,by omega⟩
      obtain ⟨g,hg⟩ := ih j (by omega) (by omega)
      exact ⟨next8 j g,state8_step j (by omega) g hg⟩

theorem supplied_alpha_base_state (g : SpiderVertex 2 0 8 → Nat)
    (hg : Graceful (spiderGraph 2 0 8) 16 g) (ha : Alpha (spiderGraph 2 0 8) 8 g)
    (hr : g .center=1) (hm : g (.arm ⟨1,by omega⟩ ⟨0,by omega⟩)=16)
    (hz : g (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)=0) : State8 2 (by omega) g := by
  refine ⟨hg,hr,hm,hz,?_⟩
  intro e
  have bound := hg.edges.bounds e
  have hgain : gains 8 8 (weight (spiderGraph 2 0 8) g e) := by
    dsimp only [gains]
    by_cases hw : weight (spiderGraph 2 0 8) g e<8
    · have mod := Nat.mod_eq_of_lt hw; rw [mod]; omega
    · omega
  exact ⟨fun _ => hgain,fun _ => ha e⟩

end GracefulBoundary.FixedEven
