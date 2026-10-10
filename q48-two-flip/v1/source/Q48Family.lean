import Q48Positions
namespace GracefulBoundary.Q48Flip
open P20Q24

def terminalWord (u : Nat) : List Nat := extend (3+2*u) (P20Q24.word u)

theorem terminal_length (u : Nat) :
    (terminalWord u).length=2*(71+24*u)+1 := by
  have h := P20Q24.all_states u
  have e := extend_length (23+24*u) (3+2*u) (P20Q24.word u) h
  simpa only [terminalWord,show 23+24*u+48=71+24*u by omega] using e

theorem terminal_sides (u : Nat) :
    (highs (terminalWord u)).Perm (List.range (72+24*u)) ∧
    (lows (terminalWord u)).Perm (List.range (71+24*u)) := by
  have h := P20Q24.all_states u
  have e := extend_sides (23+24*u) (3+2*u) (P20Q24.word u) h
  simpa only [terminalWord,show 23+24*u+49=72+24*u by omega,
    show 23+24*u+48=71+24*u by omega] using e

theorem terminal_sums (u : Nat) :
    (edgeSums (terminalWord u)).Perm (List.range (2*(71+24*u))) := by
  have h := P20Q24.all_states u
  have e := extend_sums (23+24*u) (3+2*u) (P20Q24.word u) h
  simpa only [terminalWord,show 23+24*u+48=71+24*u by omega] using e

theorem terminal_midpoint (u : Nat) :
    (terminalWord u)[71+24*u]?=some (70+24*u) := by
  have h := P20Q24.all_states u
  have e := extend_midpoint (23+24*u) (3+2*u) (P20Q24.word u) h
  simpa only [terminalWord,show 23+24*u+48=71+24*u by omega,
    show 23+24*u+47=70+24*u by omega] using e

theorem terminal_zeros (u : Nat) :
    (terminalWord u)[5+2*u]?=some 0 ∧
    (terminalWord u)[6+2*u]?=some 0 := by
  have h := P20Q24.all_states u
  have e := extend_patch (23+24*u) (3+2*u) (P20Q24.word u) h
  simpa only [terminalWord,show 3+2*u+2=5+2*u by omega,
    show 3+2*u+3=6+2*u by omega] using And.intro e.2.1 e.2.2.1

theorem terminal_certificate (u : Nat) :
    FiniteAlpha.Certificate (34+12*u) (66+22*u) (65+22*u)
      (coreLabels (142+48*u) (terminalWord u)) := by
  have hlen := terminal_length u
  have hsides := terminal_sides u
  have hedges := terminal_sums u
  have hmid := terminal_midpoint u
  have hz := terminal_zeros u
  have generic := WholeTagged.whole_path_certificate (34+12*u) (terminalWord u)
    (by simpa only [show 2*(2*(34+12*u)+3)+1=2*(71+24*u)+1 by omega] using hlen)
    (by simpa only [show 2*(34+12*u)+4=72+24*u by omega] using hsides.1)
    (by simpa only [show 2*(34+12*u)+3=71+24*u by omega] using hsides.2)
    (by simpa only [show 4*(34+12*u)+6=2*(71+24*u) by omega] using hedges)
    (by simpa only [show 2*(34+12*u)+3=71+24*u by omega,
      show 2*(34+12*u)+2=70+24*u by omega] using hmid)
  rw [show 4*(34+12*u)+6=142+48*u by omega] at generic
  refine ⟨by omega,by omega,by omega,by omega,generic,?_,?_⟩
  · rw [show 2*(34+12*u)+3-(66+22*u)=5+2*u by omega,coreLabels_lookup,hz.1]
    simp only [show ¬(5+2*u)%2=0 by omega,ite_false,Option.map_some]
  · rw [show 2*(34+12*u)+3-(65+22*u)=6+2*u by omega,coreLabels_lookup,hz.2]
    simp only [show (6+2*u)%2=0 by omega,ite_true,Option.map_some,Nat.sub_zero,
      show 4*(34+12*u)+6=142+48*u by omega]

theorem terminal_actual (u n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m (71+24*u) → Nat,
      Graceful (spiderGraph n m (71+24*u)) (n*(71+24*u)+m) f ∧
      f (.arm a ⟨66+22*u-1,by omega⟩)=0) ∧
    (∃ f : SpiderVertex n m (71+24*u) → Nat,
      Graceful (spiderGraph n m (71+24*u)) (n*(71+24*u)+m) f ∧
      f (.arm a ⟨65+22*u-1,by omega⟩)=0) := by
  have result := FiniteAlpha.prescribed_zero (34+12*u) (66+22*u) (65+22*u) n m
    (coreLabels (142+48*u) (terminalWord u)) (terminal_certificate u) hn a
  have lifted : P20Q24.DepthZero n m (2*(34+12*u)+3) (66+22*u) a ∧
      P20Q24.DepthZero n m (2*(34+12*u)+3) (65+22*u) a := by
    obtain ⟨f,hf,hz⟩ := result.1
    obtain ⟨g,hg,hm⟩ := result.2
    exact ⟨⟨by omega,f,hf,hz⟩,⟨by omega,g,hg,hm⟩⟩
  have lengthEq : 2*(34+12*u)+3=71+24*u := by omega
  rw [lengthEq] at lifted
  obtain ⟨_,f,hf,hz⟩ := lifted.1
  obtain ⟨_,g,hg,hm⟩ := lifted.2
  exact ⟨⟨f,hf,hz⟩,⟨g,hg,hm⟩⟩

/-- Separate actual-graph labelings for each selected long-arm vertex; t>=2. -/
theorem selected_actual (t n m d : Nat) (ht : 2≤t) (hn : 2≤n) (a : Fin n)
    (hd : d=21+22*t ∨ d=22+22*t) :
    ∃ (hlt : d-1<23+24*t) (f : SpiderVertex n m (23+24*t) → Nat),
      Graceful (spiderGraph n m (23+24*t)) (n*(23+24*t)+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 := by
  let u := t-2
  have pair := terminal_actual u n m hn a
  have lengthEq : 71+24*u=23+24*t := by dsimp [u]; omega
  have lowEq : 66+22*u=22+22*t := by dsimp [u]; omega
  have highEq : 65+22*u=21+22*t := by dsimp [u]; omega
  rcases hd with hd|hd
  · subst d
    have lifted : P20Q24.DepthZero n m (71+24*u) (65+22*u) a := by
      obtain ⟨f,hf,hz⟩ := pair.2
      exact ⟨by omega,f,hf,hz⟩
    have target : P20Q24.DepthZero n m (23+24*t) (21+22*t) a := by
      simpa only [← lengthEq,← highEq] using lifted
    exact target
  · subst d
    have lifted : P20Q24.DepthZero n m (71+24*u) (66+22*u) a := by
      obtain ⟨f,hf,hz⟩ := pair.1
      exact ⟨by omega,f,hf,hz⟩
    have target : P20Q24.DepthZero n m (23+24*t) (22+22*t) a := by
      simpa only [← lengthEq,← lowEq] using lifted
    exact target
end GracefulBoundary.Q48Flip
