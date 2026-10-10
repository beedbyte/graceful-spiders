import ReverseCore

namespace GracefulBoundary.ReverseComplement
open Variable

structure TrackedCore (p z t : Nat) (c : List Nat) : Prop where
  anchor : AnchoredCore p z c
  before : t+1<z-1
  maximum : c[t]?=some (p-1)
  maximumNext : c[t+1]?=some (p-1)

def Source (p b : Nat) : Prop :=
  ∃ z t c, TrackedCore p z t c ∧ b=2*p-1-t

theorem extend_prefix_lookup (g : Gadget) (p z : Nat) (c : List Nat)
    (hc : AnchoredCore p z c) (i : Nat) (hi : i<z-1) :
    (Variable.extend g z c)[(pre g).length+i]?=c[i]?.map bump9 := by
  unfold Variable.extend Variable.surgery
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  rw [show (pre g).length+i-(pre g).length=i by omega]
  rw [List.getElem?_append_left (by rw [List.length_map,part_length p z c hc]; exact hi)]
  rw [List.getElem?_map,List.getElem?_take_of_lt hi]

theorem extend_tracks_maximum (g : Gadget) (p z t : Nat) (c : List Nat)
    (hc : TrackedCore p z t c) :
    TrackedCore (p+9) (z+delta g) (t+(pre g).length) (Variable.extend g z c) := by
  have hz := hc.anchor.depth
  have hp := hc.anchor.size
  have before := hc.before
  have first := extend_prefix_lookup g p z c hc.anchor t (by omega)
  have second := extend_prefix_lookup g p z c hc.anchor (t+1) before
  rw [hc.maximum] at first
  rw [hc.maximumNext] at second
  simp only [Option.map_some] at first second
  rw [bump9_positive _ (by omega)] at first second
  have emax : p-1+9=p+9-1 := by omega
  rw [emax] at first second
  refine ⟨q9_preserves_invariant g p z c hc.anchor,?_,?_,?_⟩
  · unfold delta
    omega
  · simpa only [Nat.add_comm] using first
  · have ei : (pre g).length+(t+1)=t+(pre g).length+1 := by omega
    simpa only [ei] using second

theorem source_step_four (p b : Nat) (hb : Source p b) : Source (p+9) (b+16) := by
  obtain ⟨z,t,c,hc,he⟩ := hb
  have tracked := extend_tracks_maximum .g4 p z t c hc
  refine ⟨z+delta .g4,t+(pre .g4).length,Variable.extend .g4 z c,tracked,?_⟩
  have ht := hc.before
  have hi := hc.anchor.inside
  simp only [pre,List.length_cons,List.length_nil]
  omega

theorem source_step_six (p b : Nat) (hb : Source p b) : Source (p+9) (b+14) := by
  obtain ⟨z,t,c,hc,he⟩ := hb
  have tracked := extend_tracks_maximum .g6 p z t c hc
  refine ⟨z+delta .g6,t+(pre .g6).length,Variable.extend .g6 z c,tracked,?_⟩
  have ht := hc.before
  have hi := hc.anchor.inside
  simp only [pre,List.length_cons,List.length_nil]
  omega

theorem source_interval (p b : Nat) (hb : Source p b) (j e : Nat) (he : e≤j) :
    Source (p+9*j) (b+14*j+2*e) := by
  induction j generalizing e with
  | zero =>
    have hz : e=0 := by omega
    subst e
    simpa using hb
  | succ j ih =>
    by_cases zero : e=0
    · subst e
      have old := ih 0 (by omega)
      have next := source_step_six (p+9*j) (b+14*j+2*0) old
      simpa only [show p+9*j+9=p+9*(j+1) by omega,
        show b+14*j+2*0+14=b+14*(j+1)+2*0 by omega] using next
    · have old := ih (e-1) (by omega)
      have next := source_step_four (p+9*j) (b+14*j+2*(e-1)) old
      simpa only [show p+9*j+9=p+9*(j+1) by omega,
        show b+14*j+2*(e-1)+16=b+14*(j+1)+2*e by omega] using next

theorem source_reflects_to_coverage (p b d : Nat) (hb : Source p b)
    (hd : d=b ∨ d=b+1) : AllOdd.Coverage p d := by
  obtain ⟨z,t,c,hc,he⟩ := hb
  have hi := hc.anchor.inside
  have ht := hc.before
  have first := transform_lookup p c (t+1) hc.anchor.length (by omega)
  have second := transform_lookup p c t hc.anchor.length (by omega)
  rw [hc.maximumNext] at first
  rw [hc.maximum] at second
  simp only [Option.map_some,reflect,Nat.sub_self] at first second
  have ei : 2*p-1-(t+1)=b-1 := by omega
  rw [ei] at first
  rw [←he] at second
  apply adjacent_zeros_coverage p b d (transform p c) _ (by omega) first second hd
  exact transform_boundary p c
    ⟨by have := hc.anchor.size; omega,hc.anchor.length,hc.anchor.high,hc.anchor.low,
      hc.anchor.sums,hc.anchor.first,hc.anchor.last⟩

theorem interval_depth_selection (b j d : Nat)
    (hl : b+14*j≤d) (hu : d≤b+16*j+1) :
    ∃ e,e≤j ∧ (d=b+14*j+2*e ∨ d=b+14*j+2*e+1) := by
  refine ⟨(d-(b+14*j))/2,?_,?_⟩ <;> omega

theorem source_interval_coverage (p b : Nat) (hb : Source p b) (j d : Nat)
    (hl : b+14*j≤d) (hu : d≤b+16*j+1) : AllOdd.Coverage (p+9*j) d := by
  obtain ⟨e,he,target⟩ := interval_depth_selection b j d hl hu
  exact source_reflects_to_coverage _ _ d (source_interval p b hb j e he) target

end GracefulBoundary.ReverseComplement
