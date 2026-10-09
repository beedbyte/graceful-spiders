import ReverseSeeds

namespace GracefulBoundary.ReverseComplement
open FixedDepth

def units (p : Nat) : Nat := (p-16)/9
def corePrefix (p : Nat) : Nat := if p≤15 then 11 else if p≤24 then 27 else 25+16*units p
def depthPrefix (k : Nat) : Nat := if k≤34 then 11 else if k≤52 then 27 else 25+16*((k-35)/18)
def steps (d : Nat) : Nat := (d-10)/16
def cutoff (d : Nat) : Nat := if d≤11 then 19 else if d≤27 then 35 else 35+18*steps d

theorem core_prefix_coverage (p d : Nat) (hp : 8≤p) (hd : 2≤d ∧ d≤corePrefix p) :
    AllOdd.Coverage p d := by
  by_cases small : d≤11
  · exact AllOdd.coverage_small p d hp ⟨hd.1,small⟩
  · have dp : 12≤d := by omega
    have old := Compatible.steps_spec d dp
    by_cases initial : p≤15
    · simp only [corePrefix,initial,ite_true] at hd
      omega
    · by_cases middle : p≤24
      · have bound : d≤27 := by simpa only [corePrefix,initial,ite_false,middle,ite_true] using hd.2
        have zero : Compatible.steps d=0 := by simp [Compatible.steps,bound]
        exact Compatible.coverage_large p d dp (by rw [zero]; omega)
      · have final : d≤25+16*units p := by
          simpa only [corePrefix,initial,ite_false,middle] using hd.2
        have usize : 16+9*units p≤p := by unfold units; omega
        by_cases inherited : d≤Compatible.upper (units p)
        · have minimum := (Compatible.steps_minimal d dp).2 (units p) inherited
          exact Compatible.coverage_large p d dp (by omega)
        · apply common_residue_interval p (units p) d usize _ final
          unfold Compatible.upper at inherited
          omega

theorem odd_prefix_identity (k : Nat) (hk : 19≤k) (hodd : k%2=1) :
    corePrefix ((k-3)/2)=depthPrefix k := by
  unfold corePrefix depthPrefix units
  repeat (any_goals (first | omega | split))

theorem even_prefix_identity (k : Nat) (hk : 19≤k) (heven : k%2=0) :
    corePrefix ((k-4)/2)=depthPrefix k := by
  unfold corePrefix depthPrefix units
  repeat (any_goals (first | omega | split))

theorem odd_prescribed_zero (k n m d : Nat) (hk : 19≤k) (hodd : k%2=1)
    (hn : 2≤n) (a : Fin n) (hd : 2≤d ∧ d≤depthPrefix k) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  have eq := odd_prefix_identity k hk hodd
  obtain ⟨z,q,c,hc,target⟩ := core_prefix_coverage ((k-3)/2) d (by omega)
    ⟨hd.1,by rw [eq]; exact hd.2⟩
  have transferred := FixedDepth.core_pair_spider_transfer ((k-3)/2) z q n m c hc hn a
  have actual : Eventual.PrescribedZero n m (2*((k-3)/2)+3) d a := by
    rcases target with zero | maximum
    · subst d
      obtain ⟨f,hf,hzero⟩ := transferred.1
      exact ⟨by have := hc.zeroInside; omega,f,hf,hzero⟩
    · subst d
      obtain ⟨f,hf,hzero⟩ := transferred.2
      exact ⟨by have := hc.maxInside; omega,f,hf,hzero⟩
  have lengthEq : 2*((k-3)/2)+3=k := by omega
  rw [lengthEq] at actual
  exact actual

theorem even_prescribed_zero (k n m d : Nat) (hk : 19≤k) (heven : k%2=0)
    (hn : 2≤n) (a : Fin n) (hd : 2≤d ∧ d≤depthPrefix k) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  have eq := even_prefix_identity k hk heven
  obtain ⟨z,q,c,hc,target⟩ := core_prefix_coverage ((k-4)/2) d (by omega)
    ⟨hd.1,by rw [eq]; exact hd.2⟩
  have transferred := Even.core_pair_spider_transfer ((k-4)/2) z q n m c hc hn a
  have actual : Eventual.PrescribedZero n m (2*((k-4)/2)+4) d a := by
    rcases target with zero | maximum
    · subst d
      obtain ⟨f,hf,hzero⟩ := transferred.1
      exact ⟨by have := hc.zeroInside; omega,f,hf,hzero⟩
    · subst d
      obtain ⟨f,hf,hzero⟩ := transferred.2
      exact ⟨by have := hc.maxInside; omega,f,hf,hzero⟩
  have lengthEq : 2*((k-4)/2)+4=k := by omega
  rw [lengthEq] at actual
  exact actual

theorem all_lengths_prefix_zero (k n m d : Nat) (hk : 19≤k)
    (hn : 2≤n) (a : Fin n) (hd : 2≤d ∧ d≤depthPrefix k) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  by_cases heven : k%2=0
  · exact even_prescribed_zero k n m d hk heven hn a hd
  · exact odd_prescribed_zero k n m d hk (by omega) hn a hd

theorem steps_spec (d : Nat) (hd : 28≤d) :
    1≤steps d ∧ d≤25+16*steps d ∧ 25+16*(steps d-1)<d := by
  unfold steps
  omega

theorem steps_minimal (d : Nat) (hd : 28≤d) :
    d≤25+16*steps d ∧ ∀ u,d≤25+16*u → steps d≤u := by
  have spec := steps_spec d hd
  refine ⟨spec.2.1,?_⟩
  intro u hu
  omega

theorem cutoff_ge_nineteen (d : Nat) : 19≤cutoff d := by
  unfold cutoff
  repeat (any_goals (first | omega | split))

theorem cutoff_covers (d k : Nat) (hd : 2≤d) (hk : cutoff d≤k) :
    d≤depthPrefix k := by
  unfold cutoff depthPrefix steps at *
  repeat (any_goals (first | omega | split at hk | split))

theorem all_lengths_eventual_zero (d k n m : Nat) (hd : 2≤d)
    (hk : cutoff d≤k) (hn : 2≤n) (a : Fin n) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  exact all_lengths_prefix_zero k n m d
    (by have := cutoff_ge_nineteen d; omega) hn a ⟨hd,cutoff_covers d k hd hk⟩

theorem prefix_error_bound (k : Nat) (hk : 19≤k) :
    9*depthPrefix k≤8*k ∧ 8*k-9*depthPrefix k≤191 := by
  unfold depthPrefix
  repeat (any_goals (first | omega | split))

theorem prefix_inside (k : Nat) (hk : 19≤k) : depthPrefix k<k := by
  have bound := (prefix_error_bound k hk).1
  omega

theorem cutoff_depth_bound (d : Nat) (hd : 2≤d) : d<cutoff d := by
  have lower := cutoff_ge_nineteen d
  have cover := cutoff_covers d (cutoff d) hd (by omega)
  have inside := prefix_inside (cutoff d) lower
  omega

theorem prefix_dominates_D5 (k : Nat) :
    Compatible.depthPrefix k≤depthPrefix k := by
  unfold Compatible.depthPrefix Compatible.upper depthPrefix
  repeat (any_goals (first | omega | split))

theorem prefix_ratio_precision_limit :
    ∀ precision : Nat, ∃ cutoff : Nat, ∀ k : Nat, cutoff≤k →
      precision*distance (9*depthPrefix k) (8*k)<k := by
  intro precision
  refine ⟨192*precision+19,?_⟩
  intro k hk
  have bound := prefix_error_bound k (by omega)
  have diff : distance (9*depthPrefix k) (8*k)≤191 := by
    unfold distance
    omega
  have product := Nat.mul_le_mul_left precision diff
  have eq : precision*191=191*precision := Nat.mul_comm _ _
  omega

end GracefulBoundary.ReverseComplement
