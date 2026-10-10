import Q11Recipes

namespace GracefulBoundary.Q11

theorem growing_core_interval : ∀ p,61≤p → ∀ d,90≤d ∧ d≤F p → AllOdd.Coverage p d := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hp d hd
    by_cases base : p≤66
    · exact base_core_coverage p d ⟨hp,base⟩ hd
    · by_cases old : d≤F (p-6)
      · have previous := ih (p-6) (by omega) (by omega) d ⟨hd.1,old⟩
        have next := AllOdd.coverage_append (p-6) d previous
        simpa only [show p-6+6=p by omega] using next
      · exact bridge_coverage p d (by omega) (by omega)

theorem all_depth_core_coverage (p d : Nat) (hp : 61≤p) (hd : 2≤d ∧ d≤F p) :
    AllOdd.Coverage p d := by
  by_cases low : d≤89
  · apply ReverseComplement.core_prefix_coverage p d (by omega)
    unfold ReverseComplement.corePrefix ReverseComplement.units
    simp only [show ¬ p≤15 by omega,ite_false,show ¬ p≤24 by omega]
    omega
  · exact growing_core_interval p hp d (by omega)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem nonregression_finite :
    (List.range' 61 99).all (fun p => decide (ReverseComplement.corePrefix p≤F p))=true := by decide

theorem old_shift (p t : Nat) (hp : 61≤p) :
    ReverseComplement.corePrefix (p+99*t)=ReverseComplement.corePrefix p+176*t := by
  unfold ReverseComplement.corePrefix ReverseComplement.units
  simp only [show ¬ p+99*t≤15 by omega,ite_false,show ¬ p+99*t≤24 by omega,
    show ¬ p≤15 by omega,show ¬ p≤24 by omega]
  omega

theorem F_dominates_D6 (p : Nat) (hp : 61≤p) : ReverseComplement.corePrefix p≤F p := by
  let p0 := 61+(p-61)%99
  let t := (p-61)/99
  have hp0 : 61≤p0 ∧ p0≤159 := by dsimp only [p0]; omega
  have size : p0+99*t=p := by dsimp only [p0,t]; omega
  have member : p0∈List.range' 61 99 := by rw [List.mem_range'_1]; omega
  have base : ReverseComplement.corePrefix p0≤F p0 :=
    of_decide_eq_true ((List.all_eq_true.mp nonregression_finite) p0 member)
  have old := old_shift p0 t hp0.1
  have new := F_shift p0 (9*t) hp0.1
  rw [show p0+11*(9*t)=p by omega] at new
  rw [size] at old
  omega

end GracefulBoundary.Q11
