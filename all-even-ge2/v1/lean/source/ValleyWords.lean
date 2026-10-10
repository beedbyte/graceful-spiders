import OrdinaryCap
namespace GracefulBoundary.OrdinaryPhase

def pre : Nat → List Nat
  | 0 => [1,0]
  | t+1 => [3*t+4,3*t+3]++pre t
def up : Nat → List Nat
  | 0 => [0]
  | t+1 => up t++[3*t+2,3*t+3]
def down : Nat → List Nat
  | 0 => [1]
  | t+1 => [3*t+4,3*t+2]++down t
def valley (t : Nat) : List Nat := pre t++up t++[3*t+2,3*t+2]++down t

theorem pre_length (t : Nat) : (pre t).length=2*t+2 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [pre,ih]; omega
theorem up_length (t : Nat) : (up t).length=2*t+1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [up,ih]; omega
theorem down_length (t : Nat) : (down t).length=2*t+1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [down,ih]; omega
theorem valley_length (t : Nat) : (valley t).length=6*t+6 := by
  simp [valley,pre_length,up_length,down_length]; omega

theorem pre_first (t : Nat) : (pre t).head?=some (3*t+1) := by
  cases t with
  | zero => rfl
  | succ t => simp [pre]; omega
theorem pre_last (t : Nat) : (pre t).getLast?=some 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change ([3*t+4,3*t+3]++pre t).getLast?=some 0
    rw [List.getLast?_append,ih]; rfl
theorem up_first (t : Nat) : (up t).head?=some 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [up,List.head?_append,ih]; rfl
theorem up_last (t : Nat) : (up t).getLast?=some (3*t) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [up]; omega
theorem down_first (t : Nat) : (down t).head?=some (3*t+1) := by
  cases t with
  | zero => rfl
  | succ t => simp [down]; omega
theorem down_last (t : Nat) : (down t).getLast?=some 1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change ([3*t+4,3*t+2]++down t).getLast?=some 1
    rw [List.getLast?_append,ih]; rfl

theorem valley_last (t : Nat) : (valley t).getLast?=some 1 := by
  rw [valley,List.getLast?_append,down_last]; rfl
theorem valley_first (t : Nat) : (valley t).head?=some (3*t+1) := by
  simp [valley,pre_first]

theorem pre_sums_step (t : Nat) : edgeSums (pre (t+1))=[6*t+7,6*t+4]++edgeSums (pre t) := by
  rw [pre,FixedDepth.edgeSums_append_known _ _ _ _ (by rfl) (pre_first t)]
  simp [edgeSums]
  congr 1 <;> omega
theorem up_sums_step (t : Nat) : edgeSums (up (t+1))=edgeSums (up t)++[6*t+2,6*t+5] := by
  rw [up,FixedDepth.edgeSums_append_known _ _ _ _ (up_last t) (by rfl)]
  simp [edgeSums]
  congr 1 <;> omega
theorem down_sums_step (t : Nat) : edgeSums (down (t+1))=[6*t+6,6*t+3]++edgeSums (down t) := by
  rw [down,FixedDepth.edgeSums_append_known _ _ _ _ (by rfl) (down_first t)]
  simp [edgeSums]
  congr 1 <;> omega

theorem pre_formula (t : Nat) : pre t=(List.range (t+1)).reverse.flatMap (fun s => [3*s+1,3*s]) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [pre,List.range_succ,List.reverse_append,List.flatMap_append]
    simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [←ih]
    congr 1 <;> omega

theorem up_formula (t : Nat) : up t=0::(List.range t).flatMap (fun s => [3*s+2,3*s+3]) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [up,List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [ih]
    rfl

theorem down_formula (t : Nat) : down t=(3*t+1)::(List.range t).reverse.flatMap (fun s => [3*s+2,3*s+1]) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [down,List.range_succ,List.reverse_append,List.flatMap_append]
    simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [ih]
    congr 1 <;> omega

end GracefulBoundary.OrdinaryPhase
