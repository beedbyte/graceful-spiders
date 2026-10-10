import AllOddSeeds

namespace GracefulBoundary.AllOdd
open FixedDepth

def upper (u : Nat) : Nat := 9+14*u+2*(u/2)
def steps (d : Nat) : Nat :=
  2*((d-10)/30)+(if (d-10)%30≤13 then 1 else 2)
def cutoff (d : Nat) : Nat := if d≤11 then 19 else 19+18*steps d
def depthPrefix (k : Nat) : Nat := max 11 (upper ((k-19)/18))

theorem steps_spec (d : Nat) (hd : 12≤d) :
    1≤steps d ∧ 8+4*steps d≤d ∧ d≤upper (steps d) ∧ upper (steps d-1)<d := by
  by_cases branch : (d-10)%30≤13
  · simp only [steps,branch,ite_true,upper]
    omega
  · simp only [steps,branch,ite_false,upper]
    omega

theorem upper_monotone (u v : Nat) (h : u≤v) : upper u≤upper v := by
  unfold upper
  omega

theorem steps_minimal (d : Nat) (hd : 12≤d) :
    d≤upper (steps d) ∧ ∀ u, d≤upper u → steps d≤u := by
  have spec := steps_spec d hd
  refine ⟨spec.2.2.1,?_⟩
  intro u hu
  by_cases result : steps d≤u
  · exact result
  · have old := upper_monotone u (steps d-1) (by omega)
    have previous := spec.2.2.2
    omega

theorem coverage_append (p d : Nat) (hc : Coverage p d) : Coverage (p+6) d := by
  obtain ⟨z,q,c,hc,target⟩ := hc
  exact ⟨z,q,appendCore p c repeatedBlock,
    append_pair p 6 z q c repeatedBlock hc repeatedBlock_boundary,target⟩

theorem coverage_grow (p d : Nat) (hc : Coverage p d) (r : Nat) :
    Coverage (p+6*r) d := by
  induction r with
  | zero => simpa using hc
  | succ r ih =>
    have next := coverage_append (p+6*r) d ih
    simpa only [show p+6*r+6=p+6*(r+1) by omega] using next

theorem residue_selection (p t : Nat) (hp : 8+9*t≤p) :
    ∃ p0 r, (8≤p0 ∧ p0≤13) ∧ (p0+9*t-8)/9=t ∧ p0+9*t+6*r=p := by
  refine ⟨8+(p-(8+9*t))%6,(p-(8+9*t))/6,?_,?_,?_⟩ <;> omega

theorem coverage_from_interval (p t d : Nat) (hp : 8+9*t≤p)
    (hl : 8+4*t≤d) (hu : d≤upper t) : Coverage p d := by
  obtain ⟨p0,r,hp0,division,size⟩ := residue_selection p t hp
  obtain ⟨z,c,hc,target⟩ := Variable.Q18.theoremB_plus_cores (p0+9*t) d (by omega)
    (by rw [division]; exact hl) (by rw [division]; exact hu)
  have start : Coverage (p0+9*t) d :=
    ⟨z,z+1,c,Eventual.anchored_to_pair (p0+9*t) z c hc,target⟩
  have final := coverage_grow (p0+9*t) d start r
  rw [size] at final
  exact final

theorem coverage_small (p d : Nat) (hp : 8≤p) (hd : 2≤d ∧ d≤11) :
    Coverage p d := by
  obtain ⟨p0,r,hp0,_,size⟩ := residue_selection p 0 (by omega)
  have start := small_seed p0 d hp0 hd
  have final := coverage_grow p0 d start r
  have actual_size : p0+6*r=p := by simpa using size
  rw [actual_size] at final
  exact final

theorem coverage_large (p d : Nat) (hd : 12≤d) (hp : 8+9*steps d≤p) :
    Coverage p d := by
  have spec := steps_spec d hd
  exact coverage_from_interval p (steps d) d hp spec.2.1 spec.2.2.1

theorem cutoff_ge_nineteen (d : Nat) : 19≤cutoff d := by
  unfold cutoff
  split <;> omega

theorem cutoff_depth_bound (d : Nat) (hd : 2≤d) : d<cutoff d := by
  by_cases small : d≤11
  · simp only [cutoff,small,ite_true]
    omega
  · have spec := steps_spec d (by omega)
    simp only [cutoff,small,ite_false]
    unfold upper at spec
    omega

theorem odd_coverage (d k : Nat) (hd : 2≤d) (hodd : k%2=1)
    (hk : cutoff d≤k) : Coverage ((k-3)/2) d := by
  have nineteen := cutoff_ge_nineteen d
  by_cases small : d≤11
  · apply coverage_small _ d (by omega) ⟨hd,small⟩
  · apply coverage_large _ d (by omega)
    simp only [cutoff,small,ite_false] at hk
    omega

theorem odd_pair_certificate (d k : Nat) (hd : 2≤d) (hodd : k%2=1)
    (hk : cutoff d≤k) :
    ∃ z q c, FiniteAlpha.Certificate ((k-3)/2) z q c ∧ (d=z ∨ d=q) := by
  obtain ⟨z,q,c,hc,target⟩ := odd_coverage d k hd hodd hk
  exact ⟨z,q,completePath ((k-3)/2) c,
    core_pair_to_certificate ((k-3)/2) z q c hc,target⟩

theorem all_odd_eventual_zero (d k n m : Nat) (hd : 2≤d) (hodd : k%2=1)
    (hk : cutoff d≤k) (hn : 2≤n) (a : Fin n) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  obtain ⟨z,q,c,hc,target⟩ := odd_coverage d k hd hodd hk
  have transferred := core_pair_spider_transfer ((k-3)/2) z q n m c hc hn a
  have actual : Eventual.PrescribedZero n m (2*((k-3)/2)+3) d a := by
    rcases target with zero | maximum
    · subst d
      obtain ⟨f,hf,hzero⟩ := transferred.1
      exact ⟨by have := hc.zeroInside; omega,f,hf,hzero⟩
    · subst d
      obtain ⟨f,hf,hzero⟩ := transferred.2
      exact ⟨by have := hc.maxInside; omega,f,hf,hzero⟩
  have nineteen := cutoff_ge_nineteen d
  have lengthEq : 2*((k-3)/2)+3=k := by omega
  rw [lengthEq] at actual
  exact actual

theorem prefix_threshold (k d : Nat) (hk : 19≤k) (hd : 2≤d ∧ d≤depthPrefix k) :
    cutoff d≤k := by
  by_cases small : d≤11
  · simp only [cutoff,small,ite_true]
    exact hk
  · have height : d≤upper ((k-19)/18) := by unfold depthPrefix at hd; omega
    have minimal := (steps_minimal d (by omega)).2 ((k-19)/18) height
    simp only [cutoff,small,ite_false]
    omega

theorem prefix_inside (k : Nat) (hk : 19≤k) : depthPrefix k<k := by
  unfold depthPrefix upper
  omega

theorem all_odd_prefix_zero (k n m d : Nat) (hk : 19≤k) (hodd : k%2=1)
    (hn : 2≤n) (a : Fin n) (hd : 2≤d ∧ d≤depthPrefix k) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  exact all_odd_eventual_zero d k n m hd.1 hodd (prefix_threshold k d hk hd) hn a

theorem core_size_units (k : Nat) (hk : 19≤k) (hodd : k%2=1) :
    ((((k-3)/2)-8)/9)=(k-19)/18 := by omega

end GracefulBoundary.AllOdd
