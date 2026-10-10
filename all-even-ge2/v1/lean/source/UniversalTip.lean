import LowBand
namespace GracefulBoundary.LowBand
open EvenBoundary EvenBoundary.Flexible

def tip : Nat → List Nat
  | 0 => [0]
  | r+1 => (r+1)::r::tip r

theorem tip_head (r : Nat) : (tip r).head?=some r := by
  cases r <;> rfl

theorem tip_sums_step (r : Nat) : edgeSums (tip (r+1))=[2*r+1,2*r]++edgeSums (tip r) := by
  obtain ⟨u,hu⟩ := List.head?_eq_some_iff.mp (tip_head r)
  simp only [tip,hu,edgeSums,List.cons_append,List.nil_append]
  simp only [show r+1+r=2*r+1 by omega,show r+r=2*r by omega]

theorem tip_core (r : Nat) : FullFixed.RootZeroTip.CorePacket r (tip r) := by
  induction r with
  | zero => constructor <;> decide
  | succ r ih =>
    refine ⟨?_,?_,?_,?_,tip_head (r+1)⟩
    · simp only [tip,List.length_cons,ih.length]; omega
    · apply List.perm_iff_count.mpr
      intro x
      have old := ih.low.count_eq x
      simp only [tip,highs_cons,lows_cons,List.count_cons,List.count_append,List.count_nil,List.count_range,Nat.beq_eq_true_eq] at old ⊢
      repeat (any_goals (first | omega | split at old | split))
    · apply List.perm_iff_count.mpr
      intro x
      have old := ih.high.count_eq x
      simp only [tip,highs_cons,lows_cons,List.count_cons,List.count_range,Nat.beq_eq_true_eq] at old ⊢
      repeat (any_goals (first | omega | split at old | split))
    · rw [tip_sums_step]
      apply List.perm_iff_count.mpr
      intro x
      have old := ih.sums.count_eq x
      simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq] at old ⊢
      repeat (any_goals (first | omega | split at old | split))

theorem tip_zero (r : Nat) : (tip r)[2*r]?=some 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have idx : 2*(r+1)=2*r+2 := by omega
    simpa only [tip,idx,List.getElem?_cons_succ] using ih

theorem tip_decoded_zero (r N : Nat) : (decode N false (tip r))[2*r]?=some 0 := by
  simpa [show (2*r)%2=0 by omega] using Scattered.decode_zero_lookup N (2*r) false (tip r) (tip_zero r)

/-- Every selected long-arm tip, on the actual graph; n≥1 suffices. -/
theorem actual_tip_zero (R n m : Nat) (hR : 0<R) (hn : 1≤n) (a : Fin n) :
    ∃f : SpiderVertex n m (2*R) → Nat, Graceful (spiderGraph n m (2*R)) (n*(2*R)+m) f ∧
      f (.arm a ⟨2*R-1,by omega⟩)=0 :=
  FullFixed.supplied_tip_zero R n m hR hn (tip R) (tip_core R) (tip_decoded_zero R) a

end GracefulBoundary.LowBand
