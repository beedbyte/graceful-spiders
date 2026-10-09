import EvenTransfer
import CompatibleAsymptotic

namespace GracefulBoundary.AllLengths

def depthPrefix (k : Nat) : Nat := Compatible.depthPrefix k
def cutoff (d : Nat) : Nat := Compatible.cutoff d

theorem even_coverage (d k : Nat) (hd : 2≤d) (heven : k%2=0)
    (hk : cutoff d≤k) : AllOdd.Coverage ((k-4)/2) d := by
  have nineteen := Compatible.cutoff_ge_nineteen d
  by_cases small : d≤11
  · exact AllOdd.coverage_small _ d (by unfold cutoff at hk; omega) ⟨hd,small⟩
  · apply Compatible.coverage_large _ d (by omega)
    unfold cutoff Compatible.cutoff at hk
    simp only [small,ite_false] at hk
    omega

theorem all_even_eventual_zero (d k n m : Nat) (hd : 2≤d) (heven : k%2=0)
    (hk : cutoff d≤k) (hn : 2≤n) (a : Fin n) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  obtain ⟨z,q,c,hc,target⟩ := even_coverage d k hd heven hk
  have transferred := Even.core_pair_spider_transfer ((k-4)/2) z q n m c hc hn a
  have actual : Eventual.PrescribedZero n m (2*((k-4)/2)+4) d a := by
    rcases target with zero | maximum
    · subst d
      obtain ⟨f,hf,hzero⟩ := transferred.1
      exact ⟨by have := hc.zeroInside; omega,f,hf,hzero⟩
    · subst d
      obtain ⟨f,hf,hzero⟩ := transferred.2
      exact ⟨by have := hc.maxInside; omega,f,hf,hzero⟩
  have nineteen := Compatible.cutoff_ge_nineteen d
  have lengthEq : 2*((k-4)/2)+4=k := by unfold cutoff at hk; omega
  rw [lengthEq] at actual
  exact actual

theorem all_lengths_eventual_zero (d k n m : Nat) (hd : 2≤d)
    (hk : cutoff d≤k) (hn : 2≤n) (a : Fin n) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  by_cases heven : k%2=0
  · exact all_even_eventual_zero d k n m hd heven hk hn a
  · exact Compatible.all_odd_eventual_zero d k n m hd (by omega) hk hn a

theorem all_lengths_prefix_zero (k n m d : Nat) (hk : 19≤k)
    (hn : 2≤n) (a : Fin n) (hd : 2≤d ∧ d≤depthPrefix k) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  exact all_lengths_eventual_zero d k n m hd.1
    (Compatible.prefix_threshold k d hk hd) hn a

theorem prefix_inside (k : Nat) (hk : 19≤k) : depthPrefix k<k :=
  Compatible.prefix_inside k hk

theorem cutoff_depth_bound (d : Nat) (hd : 2≤d) : d<cutoff d :=
  Compatible.cutoff_depth_bound d hd

theorem prefix_error_bound (k : Nat) (hk : 19≤k) :
    6*depthPrefix k≤5*k ∧ 5*k-6*depthPrefix k≤104 :=
  Compatible.prefix_error_bound k hk

theorem prefix_ratio_precision_limit :
    ∀ precision : Nat, ∃ cutoff : Nat, ∀ k : Nat, cutoff≤k →
      precision*distance (6*depthPrefix k) (5*k)<k :=
  Compatible.prefix_ratio_precision_limit

end GracefulBoundary.AllLengths
