import ResidualAlpha
namespace GracefulBoundary.EvenUniform
open FixedEven

structure State (n r : Nat) (hn : 2≤n) (hr : 1≤r) (g : SpiderVertex n 0 (2*r) → Nat) : Prop where
  graceful : Graceful (spiderGraph n 0 (2*r)) (n*(2*r)) g
  root : g .center=1
  maximum : g (.arm ⟨1,by omega⟩ ⟨0,by omega⟩)=n*(2*r)
  zero : g (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)=0
  crossing : ∀e,cuts (cut n r) (g ((spiderGraph n 0 (2*r)).source e)) (g ((spiderGraph n 0 (2*r)).target e)) ↔ gains (2*r) (bridge n r) (weight (spiderGraph n 0 (2*r)) g e)

theorem supplied_alpha_state (r : Nat) (hr : 1≤r) (g : SpiderVertex 2 0 (2*r) → Nat)
    (hg : Graceful (spiderGraph 2 0 (2*r)) (2*(2*r)) g) (ha : Alpha (spiderGraph 2 0 (2*r)) (2*r) g)
    (hroot : g .center=1) (hm : g (.arm ⟨1,by omega⟩ ⟨0,by omega⟩)=2*(2*r))
    (hz : g (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)=0) : State 2 r (by omega) hr g := by
  refine ⟨hg,hroot,hm,hz,?_⟩
  intro e
  have bound := hg.edges.bounds e
  have hgain : gains (2*r) (2*r) (weight (spiderGraph 2 0 (2*r)) g e) := by
    dsimp only [gains]
    by_cases hw : weight (spiderGraph 2 0 (2*r)) g e<2*r
    · have mod := Nat.mod_eq_of_lt hw; rw [mod]; omega
    · omega
  have eqB : bridge 2 r=2*r := by simp only [bridge]; omega
  rw [eqB]
  exact ⟨fun _ => hgain,fun _ => ha e⟩

theorem initial_states (r : Nat) (hr : 3≤r) : ∃g,State 2 r (by omega) (by omega) g := by
  have paths : ∃f : Fin (2*(2*r)+1) → Nat, Graceful (pathGraph (2*(2*r))) (2*(2*r)) f ∧ Alpha (pathGraph (2*(2*r))) (2*r) f ∧
      f ⟨2*r,by omega⟩=1 ∧ f ⟨2*r+1,by omega⟩=2*(2*r) ∧ f ⟨2*r+2,by omega⟩=0 := by
    exact all_anchored_alpha_paths r hr
  obtain ⟨f,hf,ha,hrf,hm,hz⟩ := paths
  obtain ⟨g,hg,ag,hgroot,hgmax,hgzero⟩ := alpha_path_to_actual_base (2*r) (by omega) f hf ha hrf hm hz
  exact ⟨g,supplied_alpha_state r (by omega) g hg ag hgroot hgmax hgzero⟩

def next (n r : Nat) (g : SpiderVertex n 0 (2*r) → Nat) (v : SpiderVertex (n+1) 0 (2*r)) :=
  label g (cut n r) (2*r) (armLabel n r) (FixedEven.Append.toV n 0 (2*r) v)

theorem state_step (n r : Nat) (hn : 2≤n) (hr : 1≤r) (g : SpiderVertex n 0 (2*r) → Nat) (hg : State n r hn hr g) :
    State (n+1) r (by omega) hr (next n r g) := by
  have twice : n*(2*r)=2*cut n r := by simp only [cut,Nat.mul_left_comm]
  have ct := cut_positive n r (by omega) hr
  constructor
  · exact FixedEven.Append.graceful_actual n 0 (2*r) ((n+1)*(2*r)) _ (uniform_step_graceful (spiderGraph n 0 (2*r)) .center g n r hn hr hg.graceful hg.root hg.crossing)
  · dsimp only [next,FixedEven.Append.toV,label,shift]
    rw [hg.root,ite_eq_right (by omega)]
  · dsimp only [next,FixedEven.Append.toV]
    rw [dite_eq_left (by omega)]
    dsimp only [label,shift]
    rw [hg.maximum,ite_eq_left (by omega)]
    simp only [Nat.add_mul,Nat.one_mul]
  · dsimp only [next,FixedEven.Append.toV]
    rw [dite_eq_left (by omega)]
    dsimp only [label,shift]
    rw [hg.zero,ite_eq_right (by omega)]
  · intro e
    have hc := uniform_step_crossing (spiderGraph n 0 (2*r)) .center g n r hn hr hg.root hg.crossing (FixedEven.Append.toE n 0 (2*r) e)
    rw [←FixedEven.Append.source_eq,←FixedEven.Append.target_eq,←FixedEven.Append.weights] at hc
    exact hc

/-- Unbounded actual-spider induction from any supplied qualifying alpha state. -/
theorem states_from_supplied_base (r : Nat) (hr : 1≤r) (g0 : SpiderVertex 2 0 (2*r) → Nat)
    (base : State 2 r (by omega) hr g0) : ∀(n : Nat) (hn : 2≤n),∃g,State n r hn hr g := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases two : n=2
    · subst n; exact ⟨g0,base⟩
    · obtain ⟨j,rfl⟩ : ∃j,n=j+1 := ⟨n-1,by omega⟩
      obtain ⟨g,hg⟩ := ih j (by omega) (by omega)
      exact ⟨next j r g,state_step j r (by omega) hr g hg⟩

theorem uniform_residual_states (r n : Nat) (hr : 3≤r) (hn : 2≤n) : ∃g,State n r hn (by omega) g := by
  obtain ⟨g0,hg0⟩ := initial_states r hr
  exact states_from_supplied_base r (by omega) g0 hg0 n hn

theorem states_from_supplied_alpha (r : Nat) (hr : 1≤r) (g : SpiderVertex 2 0 (2*r) → Nat)
    (hg : Graceful (spiderGraph 2 0 (2*r)) (2*(2*r)) g) (ha : Alpha (spiderGraph 2 0 (2*r)) (2*r) g)
    (hroot : g .center=1) (hm : g (.arm ⟨1,by omega⟩ ⟨0,by omega⟩)=2*(2*r))
    (hz : g (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)=0) :
    ∀(n : Nat) (hn : 2≤n),∃f,State n r hn hr f :=
  states_from_supplied_base r hr g (supplied_alpha_state r hr g hg ha hroot hm hz)

end GracefulBoundary.EvenUniform
