import Q30Positions
namespace GracefulBoundary.Q30

def word : Nat → List Nat
  | 0 => seed
  | t+1 => extend (1+2*t) (word t)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem seed_state : State 17 1 seed := by constructor <;> decide

theorem all_states (t : Nat) : State (17+30*t) (1+2*t) (word t) := by
  induction t with
  | zero => exact seed_state
  | succ t ih =>
    have next := q30_preserves_state (17+30*t) (1+2*t) (word t) ih
    simpa only [word,show 17+30*t+30=17+30*(t+1) by omega,
      show 1+2*t+2=1+2*(t+1) by omega] using next

theorem family_certificate (t : Nat) :
    FiniteAlpha.Certificate (7+15*t) (16+28*t) (15+28*t)
      (coreLabels (34+60*t) (word t)) := by
  have h := all_states t
  have k : 2*(7+15*t)+3=17+30*t := by omega
  have k1 : 2*(7+15*t)+4=17+30*t+1 := by omega
  have M : 4*(7+15*t)+6=34+60*t := by omega
  have mid : 2*(7+15*t)+2=17+30*t-1 := by omega
  have generic := WholeTagged.whole_path_certificate (7+15*t) (word t)
    (by rw [k]; exact h.length) (by rw [k1]; exact h.high)
    (by rw [k]; exact h.low)
    (by rw [show 4*(7+15*t)+6=2*(17+30*t) by omega]; exact h.sums)
    (by rw [k,mid]; exact h.midpoint)
  rw [M] at generic
  refine ⟨by omega,by omega,by omega,by omega,generic,?_,?_⟩
  · rw [show 2*(7+15*t)+3-(16+28*t)=1+2*t by omega,coreLabels_lookup,h.lowZero]
    simp only [show ¬(1+2*t)%2=0 by omega,ite_false,Option.map_some]
  · rw [show 2*(7+15*t)+3-(15+28*t)=1+2*t+1 by omega,coreLabels_lookup,h.highZero]
    simp only [show (1+2*t+1)%2=0 by omega,ite_true,Option.map_some,Nat.sub_zero,M]

/-- The two specific moving depths on every actual named spider. -/
def DepthZero (n m k d : Nat) (a : Fin n) : Prop :=
  ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
    Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0

theorem actual (t n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m (17+30*t) → Nat,
      Graceful (spiderGraph n m (17+30*t)) (n*(17+30*t)+m) f ∧
      f (.arm a ⟨16+28*t-1,by omega⟩)=0) ∧
    (∃ f : SpiderVertex n m (17+30*t) → Nat,
      Graceful (spiderGraph n m (17+30*t)) (n*(17+30*t)+m) f ∧
      f (.arm a ⟨15+28*t-1,by omega⟩)=0) := by
  have result := FiniteAlpha.prescribed_zero (7+15*t) (16+28*t) (15+28*t) n m
    (coreLabels (34+60*t) (word t)) (family_certificate t) hn a
  have lifted : DepthZero n m (2*(7+15*t)+3) (16+28*t) a ∧
      DepthZero n m (2*(7+15*t)+3) (15+28*t) a := by
    obtain ⟨f,hf,hz⟩ := result.1
    obtain ⟨g,hg,hm⟩ := result.2
    exact ⟨⟨by omega,f,hf,hz⟩,⟨by omega,g,hg,hm⟩⟩
  have lengthEq : 2*(7+15*t)+3=17+30*t := by omega
  rw [lengthEq] at lifted
  obtain ⟨_,f,hf,hz⟩ := lifted.1
  obtain ⟨_,g,hg,hm⟩ := lifted.2
  exact ⟨⟨f,hf,hz⟩,⟨g,hg,hm⟩⟩

/-- Explicit selected-depth wrapper; no other long-arm depth is claimed. -/
theorem selected_actual (t n m d : Nat) (hn : 2≤n) (a : Fin n)
    (hd : d=15+28*t ∨ d=16+28*t) :
    ∃ (hlt : d-1<17+30*t) (f : SpiderVertex n m (17+30*t) → Nat),
      Graceful (spiderGraph n m (17+30*t)) (n*(17+30*t)+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 := by
  rcases hd with h|h
  · subst d
    obtain ⟨f,hf,hz⟩ := (actual t n m hn a).2
    exact ⟨by omega,f,hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (actual t n m hn a).1
    exact ⟨by omega,f,hf,hz⟩

end GracefulBoundary.Q30
