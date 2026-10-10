import H1ConcreteLookup
namespace GracefulBoundary.H1Concrete

def shift (k j : Nat) : List Nat → List Nat
  | [] => []
  | v::vs => (k+v+j%2)::shift k (j+1) vs

theorem shift_length (k j : Nat) (c : List Nat) : (shift k j c).length=c.length := by
  induction c generalizing j with
  | nil => rfl
  | cons v vs ih => simp only [shift,List.length_cons,ih]

theorem shift_lookup (k j i : Nat) (c : List Nat) :
    (shift k j c)[i]?=c[i]?.map (fun v => k+v+(j+i)%2) := by
  induction c generalizing j i with
  | nil => simp [shift]
  | cons v vs ih =>
    cases i with
    | zero => simp [shift]
    | succ i =>
      simp only [shift,List.getElem?_cons_succ,ih]
      rw [show j+1+i=j+(i+1) by omega]

theorem shift_zip (k : Nat) (c : List Nat) :
    shift k 0 c=c.zipIdx.map (fun vi => k+vi.1+vi.2%2) := by
  apply List.ext_getElem?
  intro i
  rw [shift_lookup,List.getElem?_map,List.getElem?_zipIdx]
  cases c[i]? <;> simp

theorem shift_high (k j : Nat) (c : List Nat) :
    highs (shift k j c)=(highs c).map (fun v => k+v+j%2) := by
  induction c using highs.induct generalizing j with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b xs ih =>
    simp only [shift,highs,List.map_cons,ih]
    congr 2
    funext v
    congr 1
    omega

theorem shift_low (k j : Nat) (c : List Nat) :
    lows (shift k j c)=(lows c).map (fun v => k+v+(j+1)%2) := by
  induction c using lows.induct generalizing j with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b xs ih =>
    simp only [shift,lows,List.map_cons,ih]
    congr 2
    funext v
    congr 1
    omega

theorem shift_edges (k j : Nat) (c : List Nat) :
    edgeSums (shift k j c)=(edgeSums c).map (fun v => 2*k+1+v) := by
  induction c using edgeSums.induct generalizing j with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b xs ih =>
    simp only [shift,edgeSums,List.map_cons]
    have hrec := ih (j+1)
    simp only [shift] at hrec
    rw [hrec]
    congr 1
    omega

theorem map_range_add (a b : Nat) : (List.range b).map (fun v => a+v)=List.range' a b := by
  induction b with
  | zero => rfl
  | succ b ih => simp [List.range_succ,List.range'_1_concat,ih]

theorem tail_eq_shift (p : Nat) :
    H1Append.concreteTail p=shift (2*p+3) 0 (chunks (2*p+4)) := by
  rw [shift_zip,← concrete_eq_chunks]
  rfl

end GracefulBoundary.H1Concrete
