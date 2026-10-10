import EightDepthTheorem

namespace GracefulBoundary.EvenBoundary.Flexible

/-- Decode a zero offset on either parity, without any finite packet check. -/
theorem decode_zero_at (N : Nat) (c : List Nat) (i : Nat) (b : Bool)
    (hz : c[i]? = some 0) :
    (decode N b c)[i]? =
      some (if i % 2 = 0 then (if b then N else 0) else (if b then 0 else N)) := by
  induction c generalizing i b with
  | nil => simp at hz
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hz
      subst x
      cases b <;> rfl
    | succ j =>
      have ht : xs[j]? = some 0 := by simpa using hz
      have hrec := ih j (!b) ht
      simp only [decode,List.getElem?_cons_succ] at hrec ⊢
      by_cases hj : j % 2 = 0
      · have hs : (j+1) % 2 ≠ 0 := by omega
        cases b <;> simpa [hj,hs] using hrec
      · have hs : (j+1) % 2 = 0 := by omega
        cases b <;> simpa [hj,hs] using hrec

/-- The decoded-extreme field is forced by the offset zero and parity.
    It need not be separately asserted for a newly grafted packet. -/
theorem extreme_of_core_zero (R deficit : Nat) (c : List Nat)
    (hc : CorePacket R c) (hdepth : 1 ≤ 2*R-deficit)
    (hz : c[2*R-deficit]? = some 0) :
    ExtremePacket R deficit c := by
  refine ⟨hc,hdepth,hz,?_⟩
  intro N
  have hi := decode_zero_at N c (2*R-deficit) false hz
  have parity : (2*R-deficit)%2 = deficit%2 := by omega
  simpa [extremeValue,parity] using hi

end GracefulBoundary.EvenBoundary.Flexible

#print axioms GracefulBoundary.EvenBoundary.Flexible.extreme_of_core_zero
