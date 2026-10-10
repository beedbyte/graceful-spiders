import ValleyWords
namespace GracefulBoundary.OrdinaryPhase

theorem pre_high_step (t : Nat) : highs (pre (t+1))=[3*t+4]++highs (pre t) := rfl
theorem pre_low_step (t : Nat) : lows (pre (t+1))=[3*t+3]++lows (pre t) := rfl
theorem down_high_step (t : Nat) : highs (down (t+1))=[3*t+4]++highs (down t) := rfl
theorem down_low_step (t : Nat) : lows (down (t+1))=[3*t+2]++lows (down t) := rfl
theorem up_high_step (t : Nat) : highs (up (t+1))=highs (up t)++[3*t+3] := by
  have odd : ¬(up t).length%2=0 := by rw [up_length]; omega
  rw [up,highs_append,ite_eq_right odd]; rfl
theorem up_low_step (t : Nat) : lows (up (t+1))=lows (up t)++[3*t+2] := by
  have odd : ¬(up t).length%2=0 := by rw [up_length]; omega
  rw [up,lows_append,ite_eq_right odd]; rfl

theorem valley_high_shape (t : Nat) :
    highs (valley t)=highs (pre t)++highs (up t)++[3*t+2]++lows (down t) := by
  have even : (pre t).length%2=0 := by rw [pre_length]; omega
  have odd : ¬(up t).length%2=0 := by rw [up_length]; omega
  simp [valley,List.append_assoc,highs_append,even,odd,lows]
theorem valley_low_shape (t : Nat) :
    lows (valley t)=lows (pre t)++lows (up t)++[3*t+2]++highs (down t) := by
  have even : (pre t).length%2=0 := by rw [pre_length]; omega
  have odd : ¬(up t).length%2=0 := by rw [up_length]; omega
  simp [valley,List.append_assoc,lows_append,even,odd,highs]

theorem valley_high_step (t : Nat) :
    (highs (valley (t+1))).Perm (highs (valley t)++[3*t+3,3*t+4,3*t+5]) := by
  apply List.perm_iff_count.mpr; intro x
  have next : 3*(t+1)+2=3*t+5 := by omega
  simp only [valley_high_shape,pre_high_step,up_high_step,down_low_step,next,
    List.count_append,List.count_cons,List.count_nil]
  omega
theorem valley_low_step (t : Nat) :
    (lows (valley (t+1))).Perm (lows (valley t)++[3*t+3,3*t+4,3*t+5]) := by
  apply List.perm_iff_count.mpr; intro x
  have next : 3*(t+1)+2=3*t+5 := by omega
  simp only [valley_low_shape,pre_low_step,up_low_step,down_high_step,next,
    List.count_append,List.count_cons,List.count_nil]
  omega

theorem three_new_values (t : Nat) :
    (List.range (3*t+3)++[3*t+3,3*t+4,3*t+5]).Perm (List.range (3*(t+1)+3)) := by
  apply List.perm_iff_count.mpr; intro x
  simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq]
  repeat (any_goals split)
  all_goals omega

theorem valley_sides (t : Nat) :
    (highs (valley t)).Perm (List.range (3*t+3)) ∧ (lows (valley t)).Perm (List.range (3*t+3)) := by
  induction t with
  | zero => constructor <;> decide
  | succ t ih =>
    constructor
    · exact (valley_high_step t).trans ((ih.1.append (List.Perm.refl _)).trans (three_new_values t))
    · exact (valley_low_step t).trans ((ih.2.append (List.Perm.refl _)).trans (three_new_values t))

theorem valley_sums_shape (t : Nat) :
    edgeSums (valley t)=edgeSums (pre t)++[0]++edgeSums (up t)++[6*t+2,6*t+4,6*t+3]++edgeSums (down t) := by
  have lastU : (pre t++up t).getLast?=some (3*t) := by rw [List.getLast?_append,up_last]; rfl
  have lastP : (pre t++up t++[3*t+2,3*t+2]).getLast?=some (3*t+2) := by rw [List.getLast?_append]; rfl
  have a : 3*t+(3*t+2)=6*t+2 := by omega
  have b : 3*t+2+(3*t+2)=6*t+4 := by omega
  have c : 3*t+2+(3*t+1)=6*t+3 := by omega
  rw [valley,FixedDepth.edgeSums_append_known _ _ _ _ lastP (down_first t),
    FixedDepth.edgeSums_append_known _ _ _ _ lastU (by rfl),
    FixedDepth.edgeSums_append_known _ _ _ _ (pre_last t) (up_first t)]
  simp only [edgeSums,a,b,c,Nat.zero_add,List.append_assoc,List.cons_append,List.nil_append]

theorem valley_sums_step (t : Nat) :
    (edgeSums (valley (t+1))).Perm (edgeSums (valley t)++[6*t+5,6*t+6,6*t+7,6*t+8,6*t+9,6*t+10]) := by
  apply List.perm_iff_count.mpr; intro x
  have a : 6*(t+1)+2=6*t+8 := by omega
  have b : 6*(t+1)+4=6*t+10 := by omega
  have c : 6*(t+1)+3=6*t+9 := by omega
  simp only [valley_sums_shape,pre_sums_step,up_sums_step,down_sums_step,a,b,c,
    List.count_append,List.count_cons,List.count_nil]
  omega

theorem six_new_sums (t : Nat) :
    (List.range (6*t+5)++[6*t+5,6*t+6,6*t+7,6*t+8,6*t+9,6*t+10]).Perm (List.range (6*(t+1)+5)) := by
  apply List.perm_iff_count.mpr; intro x
  simp only [List.count_append,List.count_cons,List.count_nil,List.count_range,Nat.beq_eq_true_eq]
  repeat (any_goals split)
  all_goals omega

theorem valley_sums (t : Nat) : (edgeSums (valley t)).Perm (List.range (6*t+5)) := by
  induction t with
  | zero => decide
  | succ t ih => exact (valley_sums_step t).trans ((ih.append (List.Perm.refl _)).trans (six_new_sums t))

end GracefulBoundary.OrdinaryPhase
