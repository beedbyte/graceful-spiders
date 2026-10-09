import Q11Tracking

namespace GracefulBoundary.Q11

def F (p : Nat) : Nat :=
  107+20*((p-61)/11)+4*(min ((p-61)%11) 9/2)

def baseRecipes : Nat → List Recipe
  | 61 => [⟨0,5,0,0⟩]
  | 62 => [⟨0,5,1,0⟩]
  | 63 => [⟨0,5,2,0⟩,⟨1,4,0,0⟩]
  | 64 => [⟨0,5,3,0⟩,⟨1,4,1,0⟩]
  | 65 => [⟨1,4,2,0⟩,⟨2,3,0,0⟩]
  | 66 => [⟨0,5,5,0⟩,⟨1,4,3,0⟩,⟨2,3,1,0⟩]
  | _ => []

def bridgeRecipes : Nat → List Recipe
  | 67 => [⟨1,4,4,0⟩,⟨2,3,2,0⟩,⟨3,2,0,0⟩]
  | 68 => [⟨1,4,5,0⟩,⟨2,3,3,0⟩,⟨3,2,1,0⟩]
  | 69 => [⟨2,3,4,0⟩,⟨3,2,2,0⟩,⟨4,1,0,0⟩]
  | 70 => [⟨2,3,5,0⟩,⟨0,6,0,0⟩]
  | 71 => [⟨0,6,1,0⟩]
  | 72 => [⟨0,6,2,0⟩,⟨1,5,0,0⟩]
  | 73 => [⟨0,6,3,0⟩,⟨1,5,1,0⟩]
  | 74 => [⟨0,6,4,0⟩,⟨1,5,2,0⟩,⟨2,4,0,0⟩]
  | 75 => [⟨0,6,5,0⟩,⟨1,5,3,0⟩,⟨2,4,1,0⟩]
  | 76 => [⟨1,5,4,0⟩,⟨2,4,2,0⟩,⟨3,3,0,0⟩]
  | 77 => [⟨1,5,5,0⟩,⟨2,4,3,0⟩,⟨3,3,1,0⟩]
  | _ => []

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem base_finite_cover (p : Nat) (hp : 61≤p ∧ p≤66) :
    FiniteCover p 106 (F p) (baseRecipes p) := by
  have cases : p=61 ∨ p=62 ∨ p=63 ∨ p=64 ∨ p=65 ∨ p=66 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem bridge_finite_cover (p : Nat) (hp : 67≤p ∧ p≤77) :
    FiniteCover p (F (p-6)+1) (F p) (bridgeRecipes p) := by
  have cases : p=67 ∨ p=68 ∨ p=69 ∨ p=70 ∨ p=71 ∨ p=72 ∨ p=73 ∨ p=74 ∨ p=75 ∨ p=76 ∨ p=77 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem F_shift (p t : Nat) (hp : 61≤p) : F (p+11*t)=F p+20*t := by
  unfold F
  have quotient : (p+11*t-61)/11=(p-61)/11+t := by omega
  have residue : (p+11*t-61)%11=(p-61)%11 := by omega
  rw [quotient,residue]
  omega

def liftRecipe (r : Recipe) (t : Nat) : Recipe := {r with a:=r.a+t}

theorem valid_lift (p d t : Nat) (r : Recipe) (hr : ValidRecipe p d r) :
    ValidRecipe (p+11*t) (d+20*t) (liftRecipe r t) := by
  unfold ValidRecipe liftRecipe at *
  dsimp only
  omega

theorem bridge_coverage (p d : Nat) (hp : 67≤p) (hd : F (p-6)+1≤d ∧ d≤F p) :
    AllOdd.Coverage p d := by
  let p0 := 67+(p-67)%11
  let t := (p-67)/11
  have hp0 : 67≤p0 ∧ p0≤77 := by dsimp only [p0]; omega
  have size : p0+11*t=p := by dsimp only [p0,t]; omega
  have previous : p0-6+11*t=p-6 := by omega
  have top := F_shift p0 t (by omega)
  have bottom := F_shift (p0-6) t (by omega)
  rw [size] at top
  rw [previous] at bottom
  obtain ⟨r,_,hr⟩ := finite_cover_recipe p0 (F (p0-6)+1) (F p0) (bridgeRecipes p0)
    (bridge_finite_cover p0 hp0) (d-20*t) (by omega)
  have lifted := valid_lift p0 (d-20*t) t r hr
  rw [size,show d-20*t+20*t=d by omega] at lifted
  exact recipe_coverage p d (liftRecipe r t) lifted

theorem base_core_coverage (p d : Nat) (hp : 61≤p ∧ p≤66) (hd : 90≤d ∧ d≤F p) :
    AllOdd.Coverage p d := by
  by_cases inherited : d≤105
  · apply ReverseComplement.core_prefix_coverage p d (by omega)
    unfold ReverseComplement.corePrefix ReverseComplement.units
    simp only [show ¬ p≤15 by omega,ite_false,show ¬ p≤24 by omega]
    omega
  · exact finite_cover_coverage p 106 (F p) (baseRecipes p) (base_finite_cover p hp) d (by omega)

end GracefulBoundary.Q11
