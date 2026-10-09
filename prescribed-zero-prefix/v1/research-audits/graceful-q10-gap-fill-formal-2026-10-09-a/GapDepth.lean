import GapRecipes

namespace GracefulBoundary.GapFill

def depthPrefix (k : Nat) : Nat := if k≤124 then Q11.depthPrefix k else F ((k-3)/2)

theorem all_lengths_prefix_zero (k n m d : Nat) (hk : 19≤k)
    (hn : 2≤n) (a : Fin n) (hd : 2≤d ∧ d≤depthPrefix k) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0 := by
  by_cases old : k≤124
  · simp only [depthPrefix,old,ite_true] at hd
    exact Q11.all_lengths_prefix_zero k n m d hk hn a hd
  · simp only [depthPrefix,old,ite_false] at hd
    exact Q11.coverage_spider k n m d hk (all_depth_core_coverage ((k-3)/2) d (by omega) hd) hn a

theorem F_dominates_D7 (p : Nat) : Q11.F p≤F p := by
  unfold Q11.F F
  simp only [Nat.min_def]
  repeat (any_goals (first | omega | split))

theorem prefix_dominates_D7 (k : Nat) : Q11.depthPrefix k≤depthPrefix k := by
  unfold depthPrefix Q11.depthPrefix
  split
  · omega
  · exact F_dominates_D7 ((k-3)/2)

theorem tail_error_bound (k : Nat) (hk : 125≤k) :
    11*depthPrefix k≤10*k ∧ 53≤10*k-11*depthPrefix k ∧ 10*k-11*depthPrefix k≤83 := by
  unfold depthPrefix F
  simp only [show ¬ k≤124 by omega,ite_false]
  omega

theorem prefix_error_bound (k : Nat) (hk : 19≤k) :
    11*depthPrefix k≤10*k ∧ 10*k-11*depthPrefix k≤261 := by
  by_cases old : k≤124
  · simpa only [depthPrefix,old,ite_true] using Q11.prefix_error_bound k hk
  · have bound := tail_error_bound k (by omega)
    omega

theorem prefix_inside (k : Nat) (hk : 19≤k) : depthPrefix k<k := by
  have bound := (prefix_error_bound k hk).1
  omega

theorem F_monotone (p q : Nat) (hp : 61≤p) (hpq : p≤q) : F p≤F q := by
  unfold F
  omega

theorem prefix_monotone (k l : Nat) (hk : 19≤k) (hkl : k≤l) : depthPrefix k≤depthPrefix l := by
  by_cases oldk : k≤124
  · by_cases oldl : l≤124
    · simpa only [depthPrefix,oldk,oldl,ite_true] using Q11.prefix_monotone k l hk hkl
    · have old := Q11.prefix_monotone k 125 hk (by omega)
      have value : Q11.depthPrefix 125=107 := by decide
      rw [value] at old
      have lower : 107≤F ((l-3)/2) := by unfold F; omega
      simp only [depthPrefix,oldk,oldl,ite_true,ite_false]
      omega
  · have oldl : ¬ l≤124 := by omega
    simp only [depthPrefix,oldk,oldl,ite_false]
    exact F_monotone ((k-3)/2) ((l-3)/2) (by omega) (by omega)

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

end GracefulBoundary.GapFill
