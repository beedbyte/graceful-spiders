import Q18Core
namespace GracefulBoundary.Variable.Q18

/-- A size-eighteen macro step realizes every even displacement from eight to thirty. -/
theorem paired_step (p d : Nat) (c : List Nat) (hc : AnchoredCore p d c)
    (j : Nat) (hj : j ≤ 11) : ∃ c', AnchoredCore (p+18) (d+8+2*j) c' := by
  by_cases hold : j ≤ 10
  · have h := Variable.interval_cores p d c hc 2 j (by omega)
    simpa using h
  · have he : j=11 := by omega
    subst j
    have h := q18_preserves_invariant .g30 p d c hc
    refine ⟨extend .g30 d c, ?_⟩
    have hd : d+delta .g30=d+8+2*11 := by simp [delta,pre,before]
    simpa only [hd] using h

/-- Repeating macro steps has no even-depth gaps. -/
theorem paired_interval (p d : Nat) (c : List Nat) (hc : AnchoredCore p d c)
    (t j : Nat) (hj : j ≤ 11*t) : ∃ c', AnchoredCore (p+18*t) (d+8*t+2*j) c' := by
  induction t generalizing j with
  | zero =>
    have he : j=0 := by omega
    subst j
    exact ⟨c,by simpa using hc⟩
  | succ t ih =>
    let a := min j 11
    have ha : a ≤ 11 := Nat.min_le_right _ _
    have haj : a ≤ j := Nat.min_le_left _ _
    have hprev : j-a ≤ 11*t := by dsimp only [a]; omega
    obtain ⟨old,hold⟩ := ih (j-a) hprev
    obtain ⟨next,hnext⟩ := paired_step (p+18*t) (d+8*t+2*(j-a)) old hold a ha
    refine ⟨next,?_⟩
    have hp : p+18*t+18=p+18*(t+1) := by omega
    have hd : d+8*t+2*(j-a)+8+2*a=d+8*(t+1)+2*j := by omega
    simpa only [hp,hd] using hnext

/-- t units of size nine attain every even displacement through 14t+2 floor(t/2). -/
theorem interval_cores_plus (p d : Nat) (c : List Nat) (hc : AnchoredCore p d c)
    (t j : Nat) (hj : j ≤ 5*t+t/2) :
    ∃ c', AnchoredCore (p+9*t) (d+4*t+2*j) c' := by
  let a := t/2
  let e := t%2
  have he : t=2*a+e := by dsimp only [a,e]; omega
  let j0 := min j (11*a)
  have h0 : j0 ≤ 11*a := Nat.min_le_right _ _
  have h0j : j0 ≤ j := Nat.min_le_left _ _
  have h1 : j-j0 ≤ 5*e := by dsimp only [j0,a,e] at *; omega
  obtain ⟨mid,hmid⟩ := paired_interval p d c hc a j0 h0
  obtain ⟨next,hnext⟩ := Variable.interval_cores (p+18*a) (d+8*a+2*j0) mid hmid e (j-j0) h1
  have hp : p+18*a+9*e=p+9*t := by omega
  have hd : d+8*a+2*j0+4*e+2*(j-j0)=d+4*t+2*j := by omega
  exact ⟨next,by simpa only [hp,hd] using hnext⟩

theorem interval_depth_pair_plus (d t v : Nat)
    (hl : d+4*t ≤ v) (hu : v ≤ d+14*t+2*(t/2)+1) :
    ∃ j, j ≤ 5*t+t/2 ∧ (v=d+4*t+2*j ∨ v=d+4*t+2*j+1) := by
  refine ⟨(v-(d+4*t))/2,?_,?_⟩ <;> omega

theorem theoremA_plus_cores (s v : Nat) (hs : 2 ≤ s)
    (hl : 4*s-8*((s-2)/3) ≤ v)
    (hu : v ≤ 4*s+2*((s-2)/3)+2*(((s-2)/3)/2)+1) :
    ∃ d c, AnchoredCore (3*s) d c ∧ (v=d ∨ v=d+1) := by
  let t := (s-2)/3
  let r := s-3*t
  have hr : 2 ≤ r ∧ r ≤ 4 := by dsimp only [r,t]; omega
  have hp : 3*r+9*t=3*s := by dsimp only [r,t]; omega
  have hlo : 4*r+4*t=4*s-8*t := by dsimp only [r,t]; omega
  have hhi : 4*r+14*t+2*(t/2)+1=4*s+2*t+2*(t/2)+1 := by dsimp only [r,t]; omega
  obtain ⟨c,hc⟩ := seedsA r hr
  obtain ⟨j,hj,hv⟩ := interval_depth_pair_plus (4*r) t v
    (by rw [hlo]; exact hl) (by rw [hhi]; exact hu)
  obtain ⟨c',hc'⟩ := interval_cores_plus (3*r) (4*r) c hc t j hj
  rw [hp] at hc'
  exact ⟨4*r+4*t+2*j,c',hc',hv⟩

theorem theoremB_plus_cores (p v : Nat) (hp : 8 ≤ p)
    (hl : 8+4*((p-8)/9) ≤ v)
    (hu : v ≤ 9+14*((p-8)/9)+2*(((p-8)/9)/2)) :
    ∃ d c, AnchoredCore p d c ∧ (v=d ∨ v=d+1) := by
  let t := (p-8)/9
  let r := p-9*t
  have hr : 8 ≤ r ∧ r ≤ 16 := by dsimp only [r,t]; omega
  have he : r+9*t=p := by dsimp only [r,t]; omega
  obtain ⟨c,hc⟩ := seedsB r hr
  obtain ⟨j,hj,hv⟩ := interval_depth_pair_plus 8 t v hl (by omega)
  obtain ⟨c',hc'⟩ := interval_cores_plus r 8 c hc t j hj
  rw [he] at hc'
  exact ⟨8+4*t+2*j,c',hc',hv⟩

end GracefulBoundary.Variable.Q18
