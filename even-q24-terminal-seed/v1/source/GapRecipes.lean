import Q10Tracking

namespace GracefulBoundary.GapFill
open ReverseComplement

def F (p : Nat) : Nat := 107+20*((p-61)/11)+2*((p-61)%11)

structure Recipe where
  delta : Nat
  q9 : Nat
  q10 : Nat
  q11 : Nat
  deriving DecidableEq

def firstDepth (r : Recipe) : Nat := 26+16*r.q9+18*r.q10+20*r.q11
def ValidRecipe (p d : Nat) (r : Recipe) : Prop :=
  r.delta≤1 ∧ 16+r.delta+9*r.q9+10*r.q10+11*r.q11=p ∧
  (d=firstDepth r ∨ d=firstDepth r+1)

instance (p d : Nat) (r : Recipe) : Decidable (ValidRecipe p d r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem recipe_coverage (p d : Nat) (r : Recipe) (hr : ValidRecipe p d r) : AllOdd.Coverage p d := by
  obtain ⟨hdelta,size,target⟩ := hr
  have seed := Q11.exact_seed r.delta (by omega)
  have b : Q11.seedDepth r.delta=26 := by unfold Q11.seedDepth; simp only [show r.delta≤3 by omega,ite_true]
  rw [b] at seed
  have nine := source_interval (16+r.delta) 26 seed r.q9 r.q9 (by omega)
  rw [show 26+14*r.q9+2*r.q9=26+16*r.q9 by omega] at nine
  have ten := Q10.source_iterate (16+r.delta+9*r.q9) (26+16*r.q9) nine r.q10
  have eleven := Q11.source_iterate (16+r.delta+9*r.q9+10*r.q10)
    (26+16*r.q9+18*r.q10) ten r.q11
  rw [size] at eleven
  exact source_reflects_to_coverage p (firstDepth r) d eleven target

def recipes : Nat → List Recipe
  | 62 => [⟨0,4,1,0⟩]
  | 64 => [⟨0,3,1,1⟩]
  | 66 => [⟨0,2,1,2⟩]
  | 68 => [⟨0,1,1,3⟩]
  | 70 => [⟨0,0,1,4⟩]
  | 71 => [⟨1,0,1,4⟩,⟨0,0,0,5⟩]
  | _ => []

def FiniteCover (p : Nat) : Prop :=
  (List.range' (Q11.F p+1) (F p-Q11.F p)).all
    (fun d => (recipes p).any (fun r => decide (ValidRecipe p d r)))=true

instance (p : Nat) : Decidable (FiniteCover p) := inferInstanceAs (Decidable (_=true))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem finite_gap_cover (p : Nat) (hp : 61≤p ∧ p≤71) : FiniteCover p := by
  have cases : p=61 ∨ p=62 ∨ p=63 ∨ p=64 ∨ p=65 ∨ p=66 ∨ p=67 ∨ p=68 ∨ p=69 ∨ p=70 ∨ p=71 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem finite_gap_recipe (p d : Nat) (hp : 61≤p ∧ p≤71) (hd : Q11.F p<d ∧ d≤F p) :
    ∃ r,r∈recipes p ∧ ValidRecipe p d r := by
  have mem : d∈List.range' (Q11.F p+1) (F p-Q11.F p) := by
    rw [List.mem_range'_1]
    omega
  have found := (List.all_eq_true.mp (finite_gap_cover p hp)) d mem
  obtain ⟨r,hr,valid⟩ := List.any_eq_true.mp found
  exact ⟨r,hr,of_decide_eq_true valid⟩

theorem F_shift (p t : Nat) (hp : 61≤p) : F (p+11*t)=F p+20*t := by
  unfold F
  have quotient : (p+11*t-61)/11=(p-61)/11+t := by omega
  have residue : (p+11*t-61)%11=(p-61)%11 := by omega
  rw [quotient,residue]
  omega

def liftRecipe (r : Recipe) (t : Nat) : Recipe := {r with q11:=r.q11+t}

theorem valid_lift (p d t : Nat) (r : Recipe) (hr : ValidRecipe p d r) :
    ValidRecipe (p+11*t) (d+20*t) (liftRecipe r t) := by
  unfold ValidRecipe liftRecipe firstDepth at *
  dsimp only
  omega

theorem gap_coverage (p d : Nat) (hp : 61≤p) (hd : Q11.F p<d ∧ d≤F p) :
    AllOdd.Coverage p d := by
  let p0 := 61+(p-61)%11
  let t := (p-61)/11
  have hp0 : 61≤p0 ∧ p0≤71 := by dsimp only [p0]; omega
  have size : p0+11*t=p := by dsimp only [p0,t]; omega
  have top := F_shift p0 t hp0.1
  have bottom := Q11.F_shift p0 t hp0.1
  rw [size] at top bottom
  obtain ⟨r,_,hr⟩ := finite_gap_recipe p0 (d-20*t) hp0 (by omega)
  have lifted := valid_lift p0 (d-20*t) t r hr
  rw [size,show d-20*t+20*t=d by omega] at lifted
  exact recipe_coverage p d (liftRecipe r t) lifted

theorem all_depth_core_coverage (p d : Nat) (hp : 61≤p) (hd : 2≤d ∧ d≤F p) :
    AllOdd.Coverage p d := by
  by_cases inherited : d≤Q11.F p
  · exact Q11.all_depth_core_coverage p d hp ⟨hd.1,inherited⟩
  · exact gap_coverage p d hp (by omega)

end GracefulBoundary.GapFill
