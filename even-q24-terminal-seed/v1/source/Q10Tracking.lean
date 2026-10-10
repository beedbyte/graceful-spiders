import Q10Core

namespace GracefulBoundary.Q10
open ReverseComplement

theorem extend_prefix_lookup (g : Gadget) (p z : Nat) (c : List Nat)
    (hc : AnchoredCore p z c) (i : Nat) (hi : i<z-1) :
    (extend g z c)[(pre g).length+i]?=c[i]?.map bump10 := by
  unfold extend surgery
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  rw [show (pre g).length+i-(pre g).length=i by omega]
  rw [List.getElem?_append_left (by rw [List.length_map,part_length p z c hc]; exact hi)]
  rw [List.getElem?_map,List.getElem?_take_of_lt hi]

theorem extend_tracks_maximum (g : Gadget) (p z t : Nat) (c : List Nat)
    (hc : TrackedCore p z t c) :
    TrackedCore (p+10) (z+delta g) (t+(pre g).length) (extend g z c) := by
  have hp := hc.anchor.size
  have before := hc.before
  have first := extend_prefix_lookup g p z c hc.anchor t (by omega)
  have second := extend_prefix_lookup g p z c hc.anchor (t+1) before
  rw [hc.maximum] at first
  rw [hc.maximumNext] at second
  simp only [Option.map_some] at first second
  rw [bump10_positive _ (by omega)] at first second
  have emax : p-1+10=p+10-1 := by omega
  rw [emax] at first second
  refine ⟨q10_preserves_invariant g p z c hc.anchor,?_,?_,?_⟩
  · unfold delta
    omega
  · simpa only [Nat.add_comm] using first
  · have ei : (pre g).length+(t+1)=t+(pre g).length+1 := by omega
    simpa only [ei] using second

theorem source_step (p b : Nat) (hb : Source p b) : Source (p+10) (b+18) := by
  obtain ⟨z,t,c,hc,he⟩ := hb
  have tracked := extend_tracks_maximum .g10 p z t c hc
  refine ⟨z+delta .g10,t+(pre .g10).length,extend .g10 z c,tracked,?_⟩
  have ht := hc.before
  have hi := hc.anchor.inside
  simp only [pre,List.length_cons,List.length_nil]
  omega

theorem source_iterate (p b : Nat) (hb : Source p b) (a : Nat) :
    Source (p+10*a) (b+18*a) := by
  induction a with
  | zero => simpa using hb
  | succ a ih =>
    have next := source_step (p+10*a) (b+18*a) ih
    simpa only [show p+10*a+10=p+10*(a+1) by omega,
      show b+18*a+18=b+18*(a+1) by omega] using next

end GracefulBoundary.Q10
