import H1ConcreteShift
namespace GracefulBoundary.H1Concrete

theorem chunks_length (s : Nat) : (chunks s).length=6*s := by
  simp only [chunks,List.length_append,(lengths s).1,(lengths s).2.1,(lengths s).2.2]
  omega

theorem concrete_tail (p : Nat) : H1Append.Tail p (H1Append.concreteTail p) := by
  rw [tail_eq_shift]
  have h := triple_all (2*p+4) (by omega)
  have hl : (shift (2*p+3) 0 (chunks (2*p+4))).length=12*p+24 := by
    rw [shift_length,chunks_length]; omega
  refine ⟨hl,?_,?_,?_,?_,?_,?_⟩
  · rw [shift_high]
    have hp := h.high.map (fun v => 2*p+3+v)
    simpa only [chunks,Nat.zero_mod,Nat.add_zero,map_range_add,show 3*(2*p+4)=6*p+12 by omega] using hp
  · rw [shift_low]
    have hp := h.low.map (fun v => 2*p+4+v)
    simpa only [chunks,show (0+1)%2=1 by decide,show (fun v => 2*p+3+v+1)=(fun v => 2*p+4+v) by funext v; omega,
      map_range_add,show 3*(2*p+4)=6*p+12 by omega] using hp
  · rw [shift_edges]
    have hp := h.sums.map (fun v => 4*p+7+v)
    simpa only [chunks,show 2*(2*p+3)+1=4*p+7 by omega,map_range_add,
      show 6*(2*p+4)-1=12*p+23 by omega] using hp
  · rw [List.head?_eq_getElem?,shift_lookup,chunks_lookup (2*p+4) 0 (by omega)]
    simp only [Option.map_some,coreValue,show 0<2*(2*p+4) by omega,ite_true]
  · rw [List.getLast?_eq_getElem?,hl,shift_lookup,chunks_lookup (2*p+4) (12*p+24-1) (by omega)]
    simp only [Option.map_some,coreValue,show ¬12*p+24-1<2*(2*p+4) by omega,
      show ¬12*p+24-1<4*(2*p+4) by omega,ite_false]
    congr 1 <;> omega
  · rw [shift_lookup,chunks_lookup (2*p+4) (4*p+8) (by omega)]
    simp only [Option.map_some,coreValue,show ¬4*p+8<2*(2*p+4) by omega,
      show 4*p+8<4*(2*p+4) by omega,ite_false,ite_true]
    congr 1 <;> omega

/-- Exact formerly open premise, now proved for every natural parameter. -/
theorem concreteTailInventory : H1Append.ConcreteTailInventory := concrete_tail

theorem three_bases_all (t : Nat) :
    H1Append.State (H1Append.level 0 t) (H1Append.family H1Append.concreteTail 0 H1Append.seed3 t) ∧
    H1Append.State (H1Append.level 2 t) (H1Append.family H1Append.concreteTail 2 H1Append.seed7 t) ∧
    H1Append.State (H1Append.level 7 t) (H1Append.family H1Append.concreteTail 7 H1Append.seed17 t) :=
  H1Append.concrete_three_bases_if concreteTailInventory t

/-- Separate labelings for the two named depths, with no tail-inventory premise. -/
theorem three_branches_actual (p : Nat) (hp : p=0 ∨ p=2 ∨ p=7)
    (t n m d : Nat) (hn : 2≤n) (a : Fin n)
    (hd : d=2*H1Append.level p t+1 ∨ d=2*H1Append.level p t+2) :
    ∃ (hlt : d-1<2*H1Append.level p t+3)
      (f : SpiderVertex n m (2*H1Append.level p t+3) → Nat),
      Graceful (spiderGraph n m (2*H1Append.level p t+3)) (n*(2*H1Append.level p t+3)+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 :=
  H1Append.three_branches_actual_if concreteTailInventory p hp t n m d hn a hd

end GracefulBoundary.H1Concrete
