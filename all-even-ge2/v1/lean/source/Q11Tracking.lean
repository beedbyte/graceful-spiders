import Q11Core

namespace GracefulBoundary.Q11
open ReverseComplement

theorem extend_prefix_lookup (g : Gadget) (p z : Nat) (c : List Nat)
    (hc : AnchoredCore p z c) (i : Nat) (hi : i<z-1) :
    (extend g z c)[(pre g).length+i]?=c[i]?.map bump11 := by
  unfold extend surgery
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  rw [show (pre g).length+i-(pre g).length=i by omega]
  rw [List.getElem?_append_left (by rw [List.length_map,part_length p z c hc]; exact hi)]
  rw [List.getElem?_map,List.getElem?_take_of_lt hi]

theorem extend_tracks_maximum (g : Gadget) (p z t : Nat) (c : List Nat)
    (hc : TrackedCore p z t c) :
    TrackedCore (p+11) (z+delta g) (t+(pre g).length) (extend g z c) := by
  have hp := hc.anchor.size
  have before := hc.before
  have first := extend_prefix_lookup g p z c hc.anchor t (by omega)
  have second := extend_prefix_lookup g p z c hc.anchor (t+1) before
  rw [hc.maximum] at first
  rw [hc.maximumNext] at second
  simp only [Option.map_some] at first second
  rw [bump11_positive _ (by omega)] at first second
  have emax : p-1+11=p+11-1 := by omega
  rw [emax] at first second
  refine ⟨q11_preserves_invariant g p z c hc.anchor,?_,?_,?_⟩
  · unfold delta
    omega
  · simpa only [Nat.add_comm] using first
  · have ei : (pre g).length+(t+1)=t+(pre g).length+1 := by omega
    simpa only [ei] using second

theorem source_step (p b : Nat) (hb : Source p b) : Source (p+11) (b+20) := by
  obtain ⟨z,t,c,hc,he⟩ := hb
  have tracked := extend_tracks_maximum .g11 p z t c hc
  refine ⟨z+delta .g11,t+(pre .g11).length,extend .g11 z c,tracked,?_⟩
  have ht := hc.before
  have hi := hc.anchor.inside
  simp only [pre,List.length_cons,List.length_nil]
  omega

theorem source_iterate (p b : Nat) (hb : Source p b) (a : Nat) :
    Source (p+11*a) (b+20*a) := by
  induction a with
  | zero => simpa using hb
  | succ a ih =>
    have next := source_step (p+11*a) (b+20*a) ih
    simpa only [show p+11*a+11=p+11*(a+1) by omega,
      show b+20*a+20=b+20*(a+1) by omega] using next

def seedDepth (delta : Nat) : Nat := if delta≤3 then 26 else if delta=4 then 24 else 27

theorem exact_seed (delta : Nat) (hd : delta≤5) : Source (16+delta) (seedDepth delta) := by
  have cases : delta=0 ∨ delta=1 ∨ delta=2 ∨ delta=3 ∨ delta=4 ∨ delta=5 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨16,5,Compatible.C16_16,seed16_tracks,by decide⟩
  · exact ⟨22,7,Compatible.C17_22,seed17_tracks,by decide⟩
  · exact ⟨22,9,Compatible.C18_22,seed18_tracks,by decide⟩
  · exact ⟨20,11,Compatible.C19_20,seed19_tracks,by decide⟩
  · exact ⟨24,15,Compatible.C20_24,seed20_tracks,by decide⟩
  · exact ⟨22,14,Compatible.C21_22,seed21_tracks,by decide⟩

structure Recipe where
  a : Nat
  j : Nat
  delta : Nat
  padding : Nat := 0
  deriving DecidableEq

def ValidRecipe (p d : Nat) (r : Recipe) : Prop :=
  r.delta≤5 ∧ 16+r.delta+11*r.a+9*r.j+6*r.padding=p ∧
  seedDepth r.delta+20*r.a+14*r.j≤d ∧ d≤seedDepth r.delta+20*r.a+16*r.j+1

instance (p d : Nat) (r : Recipe) : Decidable (ValidRecipe p d r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem recipe_coverage (p d : Nat) (r : Recipe) (hr : ValidRecipe p d r) : AllOdd.Coverage p d := by
  obtain ⟨hdelta,size,hl,hu⟩ := hr
  have seed := exact_seed r.delta hdelta
  have step := source_iterate (16+r.delta) (seedDepth r.delta) seed r.a
  have core := source_interval_coverage (16+r.delta+11*r.a) (seedDepth r.delta+20*r.a)
    step r.j d (by omega) (by omega)
  have final := AllOdd.coverage_grow (16+r.delta+11*r.a+9*r.j) d core r.padding
  rw [size] at final
  exact final

def FiniteCover (p lo hi : Nat) (rs : List Recipe) : Prop :=
  (List.range' lo (hi+1-lo)).all (fun d => rs.any (fun r => decide (ValidRecipe p d r)))=true

instance (p lo hi : Nat) (rs : List Recipe) : Decidable (FiniteCover p lo hi rs) :=
  inferInstanceAs (Decidable (_=true))

theorem finite_cover_recipe (p lo hi : Nat) (rs : List Recipe) (hc : FiniteCover p lo hi rs)
    (d : Nat) (hd : lo≤d ∧ d≤hi) : ∃ r,r∈rs ∧ ValidRecipe p d r := by
  have mem : d∈List.range' lo (hi+1-lo) := by
    apply List.mem_range'_1.mpr
    constructor <;> omega
  have found := (List.all_eq_true.mp hc) d mem
  obtain ⟨r,hr,hvalid⟩ := List.any_eq_true.mp found
  exact ⟨r,hr,of_decide_eq_true hvalid⟩

theorem finite_cover_coverage (p lo hi : Nat) (rs : List Recipe) (hc : FiniteCover p lo hi rs)
    (d : Nat) (hd : lo≤d ∧ d≤hi) : AllOdd.Coverage p d := by
  obtain ⟨r,_,hr⟩ := finite_cover_recipe p lo hi rs hc d hd
  exact recipe_coverage p d r hr

end GracefulBoundary.Q11
