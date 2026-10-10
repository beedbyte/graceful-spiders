import Q24Positions
namespace GracefulBoundary.P20Q24

def word : Nat → List Nat
  | 0 => seed
  | t+1 => extend (3+2*t) (word t)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem seed_state : State 23 3 seed := by constructor <;> decide

/-- The initial offset word is exactly the frozen P20 label word after decoding. -/
theorem seed_decode : coreLabels 46 seed=K23Packets.path11 := by rfl

theorem all_states (t : Nat) : State (23+24*t) (3+2*t) (word t) := by
  induction t with
  | zero => exact seed_state
  | succ t ih =>
    have next := q24_preserves_state (23+24*t) (3+2*t) (word t) ih
    simpa only [word,show 23+24*t+24=23+24*(t+1) by omega,
      show 3+2*t+2=3+2*(t+1) by omega] using next

theorem family_certificate (t : Nat) :
    FiniteAlpha.Certificate (10+12*t) (20+22*t) (19+22*t) (coreLabels (46+48*t) (word t)) := by
  have h := all_states t
  have k : 2*(10+12*t)+3=23+24*t := by omega
  have k1 : 2*(10+12*t)+4=23+24*t+1 := by omega
  have M : 4*(10+12*t)+6=46+48*t := by omega
  have mid : 2*(10+12*t)+2=23+24*t-1 := by omega
  have generic := WholeTagged.whole_path_certificate (10+12*t) (word t)
    (by rw [k]; exact h.length) (by rw [k1]; exact h.high)
    (by rw [k]; exact h.low)
    (by rw [show 4*(10+12*t)+6=2*(23+24*t) by omega]; exact h.sums)
    (by rw [k,mid]; exact h.midpoint)
  rw [M] at generic
  refine ⟨by omega,by omega,by omega,by omega,generic,?_,?_⟩
  · rw [show 2*(10+12*t)+3-(20+22*t)=3+2*t by omega,coreLabels_lookup,h.lowZero]
    simp only [show ¬(3+2*t)%2=0 by omega,ite_false,Option.map_some]
  · rw [show 2*(10+12*t)+3-(19+22*t)=3+2*t+1 by omega,coreLabels_lookup,h.highZero]
    simp only [show (3+2*t+1)%2=0 by omega,ite_true,Option.map_some,Nat.sub_zero,M]

/-- Both separate prescribed-zero conclusions, on every actual named arm. -/
def DepthZero (n m k d : Nat) (a : Fin n) : Prop :=
  ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
    Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0

theorem q24_actual (t n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m (23+24*t) → Nat,
      Graceful (spiderGraph n m (23+24*t)) (n*(23+24*t)+m) f ∧
      f (.arm a ⟨20+22*t-1,by omega⟩)=0) ∧
    (∃ f : SpiderVertex n m (23+24*t) → Nat,
      Graceful (spiderGraph n m (23+24*t)) (n*(23+24*t)+m) f ∧
      f (.arm a ⟨19+22*t-1,by omega⟩)=0) := by
  have result := FiniteAlpha.prescribed_zero (10+12*t) (20+22*t) (19+22*t) n m
    (coreLabels (46+48*t) (word t)) (family_certificate t) hn a
  have lifted : DepthZero n m (2*(10+12*t)+3) (20+22*t) a ∧
      DepthZero n m (2*(10+12*t)+3) (19+22*t) a := by
    obtain ⟨f,hf,hz⟩ := result.1
    obtain ⟨g,hg,hm⟩ := result.2
    exact ⟨⟨by omega,f,hf,hz⟩,⟨by omega,g,hg,hm⟩⟩
  have lengthEq : 2*(10+12*t)+3=23+24*t := by omega
  rw [lengthEq] at lifted
  obtain ⟨_,f,hf,hz⟩ := lifted.1
  obtain ⟨_,g,hg,hm⟩ := lifted.2
  exact ⟨⟨f,hf,hz⟩,⟨g,hg,hm⟩⟩

/-- A selected member of the exact two-depth progression; no other depths claimed. -/
theorem selected_actual (t n m d : Nat) (hn : 2≤n) (a : Fin n)
    (hd : d=19+22*t ∨ d=20+22*t) :
    ∃ (hlt : d-1<23+24*t) (f : SpiderVertex n m (23+24*t) → Nat),
      Graceful (spiderGraph n m (23+24*t)) (n*(23+24*t)+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 := by
  rcases hd with h|h
  · subst d
    obtain ⟨f,hf,hz⟩ := (q24_actual t n m hn a).2
    exact ⟨by omega,f,hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (q24_actual t n m hn a).1
    exact ⟨by omega,f,hf,hz⟩

end GracefulBoundary.P20Q24
