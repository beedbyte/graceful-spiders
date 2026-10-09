import Q11Prefix

namespace GracefulBoundary.Q11
open FixedDepth

def depthPrefix (k : Nat) : Nat := if k≤124 then ReverseComplement.depthPrefix k else F ((k-3)/2)

theorem coverage_spider (k n m d : Nat) (hk : 19≤k)
    (hc : AllOdd.Coverage ((k-3)/2) d) (hn : 2≤n) (a : Fin n) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  obtain ⟨z,q,c,hcore,target⟩ := hc
  by_cases heven : k%2=0
  · have transferred := Even.core_pair_spider_transfer ((k-3)/2) z q n m c hcore hn a
    have actual : Eventual.PrescribedZero n m (2*((k-3)/2)+4) d a := by
      rcases target with zero | maximum
      · subst d
        obtain ⟨f,hf,hzero⟩ := transferred.1
        exact ⟨by have := hcore.zeroInside; omega,f,hf,hzero⟩
      · subst d
        obtain ⟨f,hf,hzero⟩ := transferred.2
        exact ⟨by have := hcore.maxInside; omega,f,hf,hzero⟩
    have lengthEq : 2*((k-3)/2)+4=k := by omega
    rw [lengthEq] at actual
    exact actual
  · have transferred := FixedDepth.core_pair_spider_transfer ((k-3)/2) z q n m c hcore hn a
    have actual : Eventual.PrescribedZero n m (2*((k-3)/2)+3) d a := by
      rcases target with zero | maximum
      · subst d
        obtain ⟨f,hf,hzero⟩ := transferred.1
        exact ⟨by have := hcore.zeroInside; omega,f,hf,hzero⟩
      · subst d
        obtain ⟨f,hf,hzero⟩ := transferred.2
        exact ⟨by have := hcore.maxInside; omega,f,hf,hzero⟩
    have lengthEq : 2*((k-3)/2)+3=k := by omega
    rw [lengthEq] at actual
    exact actual

theorem all_lengths_prefix_zero (k n m d : Nat) (hk : 19≤k)
    (hn : 2≤n) (a : Fin n) (hd : 2≤d ∧ d≤depthPrefix k) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  by_cases old : k≤124
  · simp only [depthPrefix,old,ite_true] at hd
    exact ReverseComplement.all_lengths_prefix_zero k n m d hk hn a hd
  · simp only [depthPrefix,old,ite_false] at hd
    exact coverage_spider k n m d hk (all_depth_core_coverage ((k-3)/2) d (by omega) hd) hn a

theorem prefix_error_bound (k : Nat) (hk : 19≤k) :
    11*depthPrefix k≤10*k ∧ 10*k-11*depthPrefix k≤261 := by
  unfold depthPrefix ReverseComplement.depthPrefix F
  simp only [Nat.min_def]
  repeat (any_goals (first | omega | split))

theorem prefix_inside (k : Nat) (hk : 19≤k) : depthPrefix k<k := by
  have bound := (prefix_error_bound k hk).1
  omega

theorem prefix_dominates_D6 (k : Nat) (hk : 19≤k) : ReverseComplement.depthPrefix k≤depthPrefix k := by
  by_cases old : k≤124
  · simp only [depthPrefix,old,ite_true]
    omega
  · simp only [depthPrefix,old,ite_false]
    have bound := F_dominates_D6 ((k-3)/2) (by omega)
    by_cases heven : k%2=0
    · have eq := ReverseComplement.even_prefix_identity k hk heven
      have sizes : (k-4)/2=(k-3)/2 := by omega
      rw [sizes] at eq
      rw [eq] at bound
      exact bound
    · have eq := ReverseComplement.odd_prefix_identity k hk (by omega)
      rw [eq] at bound
      exact bound

theorem F_monotone (p q : Nat) (hp : 61≤p) (hpq : p≤q) : F p≤F q := by
  unfold F
  simp only [Nat.min_def]
  repeat (any_goals (first | omega | split))

theorem prefix_monotone (k l : Nat) (hk : 19≤k) (hkl : k≤l) : depthPrefix k≤depthPrefix l := by
  by_cases oldk : k≤124
  · by_cases oldl : l≤124
    · simp only [depthPrefix,oldk,oldl,ite_true]
      unfold ReverseComplement.depthPrefix
      repeat (any_goals (first | omega | split))
    · have upper : ReverseComplement.depthPrefix k≤89 := by
        unfold ReverseComplement.depthPrefix
        repeat (any_goals (first | omega | split))
      have lower : 107≤F ((l-3)/2) := by unfold F; omega
      simp only [depthPrefix,oldk,oldl,ite_true,ite_false]
      omega
  · have oldl : ¬ l≤124 := by omega
    simp only [depthPrefix,oldk,oldl,ite_false]
    exact F_monotone ((k-3)/2) ((l-3)/2) (by omega) (by omega)

def steps (d : Nat) : Nat := (d-104)/20
def substeps (d : Nat) : Nat := ((d-104)%20)/4
def cutoff (d : Nat) : Nat := if d≤89 then ReverseComplement.cutoff d else 125+22*steps d+4*substeps d

theorem cutoff_ge_nineteen (d : Nat) : 19≤cutoff d := by
  unfold cutoff
  split
  · exact ReverseComplement.cutoff_ge_nineteen d
  · omega

theorem large_cutoff_spec (d : Nat) (hd : 90≤d) :
    substeps d≤4 ∧ d≤depthPrefix (125+22*steps d+4*substeps d) ∧
      depthPrefix (124+22*steps d+4*substeps d)<d := by
  unfold substeps steps depthPrefix ReverseComplement.depthPrefix F
  simp only [Nat.min_def]
  repeat (any_goals (first | omega | split))

theorem cutoff_covers (d : Nat) (hd : 2≤d) : d≤depthPrefix (cutoff d) := by
  by_cases small : d≤89
  · simp only [cutoff,small,ite_true]
    have old := ReverseComplement.cutoff_covers d (ReverseComplement.cutoff d) hd (by omega)
    have compare := prefix_dominates_D6 (ReverseComplement.cutoff d) (ReverseComplement.cutoff_ge_nineteen d)
    omega
  · simp only [cutoff,small,ite_false]
    exact (large_cutoff_spec d (by omega)).2.1

theorem cutoff_previous_fails (d : Nat) (hd : 2≤d) (hprevious : 19≤cutoff d-1) :
    depthPrefix (cutoff d-1)<d := by
  by_cases small : d≤89
  · unfold cutoff at hprevious ⊢
    simp only [small,ite_true] at hprevious ⊢
    unfold ReverseComplement.cutoff ReverseComplement.steps at hprevious
    unfold ReverseComplement.cutoff ReverseComplement.steps depthPrefix ReverseComplement.depthPrefix F
    simp only [Nat.min_def]
    repeat (any_goals (first | omega | split at hprevious | split))
  · simp only [cutoff,small,ite_false]
    have previous := (large_cutoff_spec d (by omega)).2.2
    simpa only [show 125+22*steps d+4*substeps d-1=124+22*steps d+4*substeps d by omega] using previous

theorem cutoff_minimal (d k : Nat) (hd : 2≤d) (hk : 19≤k) (hcoverage : d≤depthPrefix k) :
    cutoff d≤k := by
  by_cases covered : cutoff d≤k
  · exact covered
  · have previous := cutoff_previous_fails d hd (by omega)
    have monotone := prefix_monotone k (cutoff d-1) hk (by omega)
    omega

theorem all_lengths_eventual_zero (d k n m : Nat) (hd : 2≤d)
    (hk : cutoff d≤k) (hn : 2≤n) (a : Fin n) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  have minimum := cutoff_ge_nineteen d
  have covers := cutoff_covers d hd
  have monotone := prefix_monotone (cutoff d) k minimum hk
  exact all_lengths_prefix_zero k n m d (by omega) hn a ⟨hd,by omega⟩

theorem cutoff_depth_bound (d : Nat) (hd : 2≤d) : d<cutoff d := by
  have covers := cutoff_covers d hd
  have inside := prefix_inside (cutoff d) (cutoff_ge_nineteen d)
  omega

theorem prefix_ratio_precision_limit :
    ∀ precision : Nat, ∃ cutoff : Nat, ∀ k : Nat, cutoff≤k →
      precision*distance (11*depthPrefix k) (10*k)<k := by
  intro precision
  refine ⟨262*precision+19,?_⟩
  intro k hk
  have bound := prefix_error_bound k (by omega)
  have diff : distance (11*depthPrefix k) (10*k)≤261 := by unfold distance; omega
  have product := Nat.mul_le_mul_left precision diff
  have eq : precision*261=261*precision := Nat.mul_comm _ _
  omega

end GracefulBoundary.Q11
