import CompatibleSeeds

namespace GracefulBoundary.Compatible
open FixedDepth

def upper (u : Nat) : Nat := 27+14*u+2*(u/2)
def steps (d : Nat) : Nat := if d≤27 then 0 else
  2*((d-28)/30)+(if (d-28)%30≤13 then 1 else 2)
def cutoff (d : Nat) : Nat := if d≤11 then 19 else 35+18*steps d
def depthPrefix (k : Nat) : Nat := if k≤34 then 11 else upper ((k-35)/18)

theorem steps_spec (d : Nat) (hd : 12≤d) :
    12+4*steps d≤d ∧ d≤upper (steps d) := by
  by_cases small : d≤27
  · simp [steps,small,upper,hd]
  · by_cases branch : (d-28)%30≤13
    · simp only [steps,small,ite_false,branch,ite_true,upper]
      omega
    · simp only [steps,small,ite_false,branch,ite_false,upper]
      omega

theorem upper_monotone (u v : Nat) (h : u≤v) : upper u≤upper v := by
  unfold upper
  omega

theorem steps_minimal (d : Nat) (hd : 12≤d) :
    d≤upper (steps d) ∧ ∀ u, d≤upper u → steps d≤u := by
  refine ⟨(steps_spec d hd).2,?_⟩
  intro u hu
  by_cases small : d≤27
  · simp only [steps,small,ite_true]
    omega
  · have previous : upper (steps d-1)<d := by
      by_cases branch : (d-28)%30≤13
      · simp only [steps,small,ite_false,branch,ite_true,upper]
        omega
      · simp only [steps,small,ite_false,branch,ite_false,upper]
        omega
    by_cases result : steps d≤u
    · exact result
    · have old := upper_monotone u (steps d-1) (by omega)
      omega

theorem seed_interval_selection (t d : Nat)
    (hl : 12+4*t≤d) (hu : d≤upper t) :
    ∃ a j, (12≤a ∧ a≤26 ∧ a%2=0) ∧ j≤5*t+t/2 ∧
      (d=a+4*t+2*j ∨ d=a+4*t+2*j+1) := by
  let w := (d-(12+4*t))/2
  let b := min w 7
  refine ⟨12+2*b,w-b,?_,?_,?_⟩
  all_goals dsimp only [b,w] at *
  all_goals unfold upper at hu
  all_goals omega

theorem residue_selection (p t : Nat) (hp : 16+9*t≤p) :
    ∃ p0 r, (16≤p0 ∧ p0≤21) ∧ p0+9*t+6*r=p := by
  refine ⟨16+(p-(16+9*t))%6,(p-(16+9*t))/6,?_,?_⟩ <;> omega

theorem coverage_from_interval (p t d : Nat) (hp : 16+9*t≤p)
    (hl : 12+4*t≤d) (hu : d≤upper t) : AllOdd.Coverage p d := by
  obtain ⟨p0,r,hp0,size⟩ := residue_selection p t hp
  obtain ⟨a,j,ha,hj,target⟩ := seed_interval_selection t d hl hu
  obtain ⟨c,hc⟩ := compatible_seed p0 a hp0 ha
  obtain ⟨next,hnext⟩ := Variable.Q18.interval_cores_plus p0 a c hc t j hj
  have start : AllOdd.Coverage (p0+9*t) d :=
    ⟨a+4*t+2*j,a+4*t+2*j+1,next,
      Eventual.anchored_to_pair _ _ _ hnext,target⟩
  have final := AllOdd.coverage_grow (p0+9*t) d start r
  rw [size] at final
  exact final

theorem coverage_large (p d : Nat) (hd : 12≤d) (hp : 16+9*steps d≤p) :
    AllOdd.Coverage p d := by
  exact coverage_from_interval p (steps d) d hp (steps_spec d hd).1 (steps_spec d hd).2

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
    (hk : cutoff d≤k) : AllOdd.Coverage ((k-3)/2) d := by
  have nineteen := cutoff_ge_nineteen d
  by_cases small : d≤11
  · exact AllOdd.coverage_small _ d (by omega) ⟨hd,small⟩
  · apply coverage_large _ d (by omega)
    simp only [cutoff,small,ite_false] at hk
    omega

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
  · have large : 35≤k := by unfold depthPrefix at hd; split at hd <;> omega
    have height : d≤upper ((k-35)/18) := by
      unfold depthPrefix at hd
      simp only [show ¬ k≤34 by omega,ite_false] at hd
      exact hd.2
    have minimal := (steps_minimal d (by omega)).2 ((k-35)/18) height
    simp only [cutoff,small,ite_false]
    omega

theorem prefix_inside (k : Nat) (hk : 19≤k) : depthPrefix k<k := by
  unfold depthPrefix upper
  split <;> omega

theorem all_odd_prefix_zero (k n m d : Nat) (hk : 19≤k) (hodd : k%2=1)
    (hn : 2≤n) (a : Fin n) (hd : 2≤d ∧ d≤depthPrefix k) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  exact all_odd_eventual_zero d k n m hd.1 hodd (prefix_threshold k d hk hd) hn a

end GracefulBoundary.Compatible
