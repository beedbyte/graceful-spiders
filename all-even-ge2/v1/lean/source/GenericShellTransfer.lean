import EightDepthTheorem

namespace GracefulBoundary.EvenBoundary

open Flexible

/-- A complete target-radius packet, from any source, gives a zero at the
    named selected arm and prescribed deficit on the actual spider. -/
theorem named_arm_zero_from_packet (r n m deficit : Nat)
    (hr : 3 ≤ r) (hn : 2 ≤ n) (a : Fin n)
    (c : List Nat) (hc : ExtremePacket r deficit c) :
    ∃ (hlt : 2*r-deficit-1 < 2*r) (f : SpiderVertex n m (2*r) → Nat),
      Graceful (spiderGraph n m (2*r)) (n*(2*r)+m) f ∧
      f (.arm a ⟨2*r-deficit-1,hlt⟩) = 0 := by
  obtain ⟨h,rfl⟩ : ∃ h, n=h+1 := ⟨n-1,by omega⟩
  obtain ⟨g,hg,hroot⟩ := nonempty_even_residual r h m hr (by omega)
  obtain ⟨f,hf,htarget⟩ :=
    extreme_packet_attachment (spiderGraph h m (2*r)) .center
      (h*(2*r)+m) r deficit c hc g hg hroot
  rw [flexible_shell_graph] at hf
  have size : h*(2*r)+m+2*r=(h+1)*(2*r)+m := by
    simp only [Nat.add_mul,Nat.one_mul,Nat.add_right_comm]
  rw [size] at hf htarget
  let actual : SpiderVertex (h+1) m (2*r) → Nat :=
    fun v => f (FixedEven.Append.toV h m (2*r) v)
  have hactual : Graceful (spiderGraph (h+1) m (2*r)) ((h+1)*(2*r)+m) actual :=
    FixedEven.Append.graceful_actual h m (2*r) _ f hf
  let last : Fin (h+1) := ⟨h,by omega⟩
  let selected : SpiderVertex (h+1) m (2*r) → Nat :=
    fun v => actual (NearTip.swapVertex a last v)
  have hselected : Graceful (spiderGraph (h+1) m (2*r)) ((h+1)*(2*r)+m) selected :=
    NearTip.graceful_swap a last actual hactual
  have hlast : actual (.arm last ⟨2*r-deficit-1,by have := hc.depthPositive; omega⟩) =
      extremeValue ((h+1)*(2*r)+m) deficit := by
    simpa only [actual,last,FixedEven.Append.toV,Nat.lt_irrefl,dite_false] using htarget
  have hval : selected (.arm a ⟨2*r-deficit-1,by have := hc.depthPositive; omega⟩) =
      extremeValue ((h+1)*(2*r)+m) deficit := by
    simpa only [selected,NearTip.swapVertex,NearTip.swapIndex_first] using hlast
  have hlt : 2*r-deficit-1 < 2*r := by have := hc.depthPositive; omega
  by_cases heven : deficit % 2 = 0
  · refine ⟨hlt,selected,hselected,?_⟩
    simpa [extremeValue,heven] using hval
  · have hmax : selected (.arm a ⟨2*r-deficit-1,hlt⟩) =
        (h+1)*(2*r)+m := by
      simpa [extremeValue,heven] using hval
    exact ⟨hlt,complementLabel _ selected,
      whole_graph_graceful_complement _ _ selected hselected,
      complement_maximum_zero _ selected _ hmax⟩

/-- Nonvacuous two-arm, one-leaf odd-deficit boundary; this uses complement. -/
example (a : Fin 2) :
    ∃ (hlt : 2*5-1-1 < 2*5) (f : SpiderVertex 2 1 (2*5) → Nat),
      Graceful (spiderGraph 2 1 (2*5)) (2*(2*5)+1) f ∧
      f (.arm a ⟨2*5-1-1,hlt⟩) = 0 :=
  named_arm_zero_from_packet 5 2 1 1 (by omega) (by omega) a s52 s52_c1

/-- Nonvacuous two-arm, no-leaf even-deficit boundary. -/
example (a : Fin 2) :
    ∃ (hlt : 2*9-8-1 < 2*9) (f : SpiderVertex 2 0 (2*9) → Nat),
      Graceful (spiderGraph 2 0 (2*9)) (2*(2*9)+0) f ∧
      f (.arm a ⟨2*9-8-1,hlt⟩) = 0 :=
  named_arm_zero_from_packet 9 2 0 8 (by omega) (by omega) a s98 s98_c8

end GracefulBoundary.EvenBoundary

#print axioms GracefulBoundary.EvenBoundary.named_arm_zero_from_packet
