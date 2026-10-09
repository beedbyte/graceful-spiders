import FixedDepthSeeds
import Q18Interval

namespace GracefulBoundary.Eventual
open FixedDepth

def units (d : Nat) : Nat := (d-8)/4
def threshold (d : Nat) : Nat := 3+3*units d

def Coverage (s d : Nat) : Prop :=
  ∃ z q c, CorePair (3*s) z q c ∧ (d=z ∨ d=q)

def PrescribedZero (n m k d : Nat) (a : Fin n) : Prop :=
  ∃ (hdepth : d-1<k) (f : SpiderVertex n m k → Nat),
    Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hdepth⟩)=0

theorem anchored_to_pair (p z : Nat) (c : List Nat)
    (hc : Variable.AnchoredCore p z c) : CorePair p z (z+1) c := by
  refine ⟨⟨by have := hc.size; omega,hc.length,hc.high,hc.low,hc.sums,hc.first,hc.last⟩,
    by have := hc.depth; omega,by have := hc.inside; omega,hc.even,
    by omega,by have := hc.inside; omega,by have := hc.even; omega,hc.zeroL,?_⟩
  simpa only [Nat.add_sub_cancel] using hc.zeroH

theorem b_plus_coverage (u d : Nat)
    (hl : 8+4*u≤d) (hu : d≤9+14*u+2*(u/2)) : Coverage (3+3*u) d := by
  have division : (9+9*u-8)/9=u := by omega
  obtain ⟨z,c,hc,target⟩ := Variable.Q18.theoremB_plus_cores (9+9*u) d (by omega)
    (by rw [division]; exact hl) (by rw [division]; exact hu)
  have pair := anchored_to_pair (9+9*u) z c hc
  have size : 9+9*u=3*(3+3*u) := by omega
  rw [size] at pair
  exact ⟨z,z+1,c,pair,target⟩

theorem coverage_step (s d : Nat) (hc : Coverage s d) : Coverage (s+2) d := by
  obtain ⟨z,q,c,hc,target⟩ := hc
  have extended := append_pair (3*s) 6 z q c repeatedBlock hc repeatedBlock_boundary
  have size : 3*s+6=3*(s+2) := by omega
  rw [size] at extended
  exact ⟨z,q,appendCore (3*s) c repeatedBlock,extended,target⟩

theorem overlap_windows (d : Nat) (hd : 16≤d) :
    2≤units d ∧
    (8+4*(units d-1)≤d ∧ d≤9+14*(units d-1)+2*((units d-1)/2)) ∧
    (8+4*units d≤d ∧ d≤9+14*units d+2*(units d/2)) := by
  unfold units
  omega

theorem consecutive_closure (P : Nat → Prop) (b : Nat)
    (hb : P b) (hb1 : P (b+1)) (step : ∀ r, P r → P (r+2)) :
    ∀ r, P (b+r) := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    by_cases zero : r=0
    · subst r; simpa using hb
    by_cases one : r=1
    · subst r; exact hb1
    have previous := ih (r-2) (by omega)
    have next := step (b+(r-2)) previous
    simpa only [show b+(r-2)+2=b+r by omega] using next

theorem eventual_coverage (d s : Nat) (hd : 16≤d) (hs : threshold d≤s) :
    Coverage s d := by
  have windows := overlap_windows d hd
  have small := b_plus_coverage (units d-1) d windows.2.1.1 windows.2.1.2
  have large := b_plus_coverage (units d) d windows.2.2.1 windows.2.2.2
  have next := coverage_step _ d (coverage_step _ d small)
  have sizes : 3+3*(units d-1)+2+2=threshold d+1 := by
    have := windows.1
    unfold threshold
    omega
  rw [sizes] at next
  change Coverage (threshold d) d at large
  have all := consecutive_closure (fun s => Coverage s d) (threshold d) large next
    (fun s hc => coverage_step s d hc)
  have result := all (s-threshold d)
  simpa only [show threshold d+(s-threshold d)=s by omega] using result

theorem eventual_depth_bound (d s : Nat) (hd : 16≤d) (hs : threshold d≤s) :
    d-1<6*s+3 := by
  unfold threshold units at hs
  omega

/-- Every fixed depth d>=16 occurs at every sufficiently long arm length in
    the specified congruence class, with all spider parameters and arms free. -/
theorem eventual_fixed_depth_zero (d s n m : Nat) (hd : 16≤d)
    (hs : 3+3*((d-8)/4)≤s) (hn : 2≤n) (a : Fin n) :
    ∃ (hlt : d-1<6*s+3) (f : SpiderVertex n m (6*s+3) → Nat),
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 := by
  obtain ⟨z,q,c,hc,target⟩ := eventual_coverage d s hd hs
  have transferred := core_pair_spider_transfer (3*s) z q n m c hc hn a
  have actual : PrescribedZero n m (2*(3*s)+3) d a := by
    rcases target with zero | maximum
    · subst d
      obtain ⟨f,hf,hzero⟩ := transferred.1
      exact ⟨by have := hc.zeroInside; omega,f,hf,hzero⟩
    · subst d
      obtain ⟨f,hf,hzero⟩ := transferred.2
      exact ⟨by have := hc.maxInside; omega,f,hf,hzero⟩
  have lengthEq : 2*(3*s)+3=6*s+3 := by omega
  rw [lengthEq] at actual
  exact actual

end GracefulBoundary.Eventual
