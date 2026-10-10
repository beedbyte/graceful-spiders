import VariableCore
namespace GracefulBoundary.Variable

theorem gadget_for_increment (a : Nat) (ha : a ≤ 5) : ∃ g,delta g=4+2*a := by
  have he : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨.g4,rfl⟩
  · exact ⟨.g6,rfl⟩
  · exact ⟨.g8,rfl⟩
  · exact ⟨.g10,rfl⟩
  · exact ⟨.g12,rfl⟩
  · exact ⟨.g14,rfl⟩

/-- Every even displacement between 4t and 14t is realized by q9 surgery. -/
theorem interval_cores (p d : Nat) (c : List Nat) (hc : AnchoredCore p d c)
    (t j : Nat) (hj : j ≤ 5*t) : ∃ c',AnchoredCore (p+9*t) (d+4*t+2*j) c' := by
  induction t generalizing j with
  | zero =>
    have he : j=0 := by omega
    subst j
    exact ⟨c,by simpa using hc⟩
  | succ t ih =>
    let a := min j 5
    have ha : a ≤ 5 := Nat.min_le_right _ _
    have haj : a ≤ j := Nat.min_le_left _ _
    have hprev : j-a ≤ 5*t := by dsimp only [a]; omega
    obtain ⟨old,hold⟩ := ih (j-a) hprev
    obtain ⟨g,hg⟩ := gadget_for_increment a ha
    have hn := q9_preserves_invariant g (p+9*t) (d+4*t+2*(j-a)) old hold
    refine ⟨extend g (d+4*t+2*(j-a)) old,?_⟩
    have hp : p+9*t+9=p+9*(t+1) := by omega
    have hd : d+4*t+2*(j-a)+delta g=d+4*(t+1)+2*j := by rw [hg]; omega
    simpa only [hp,hd] using hn

/-- Each integer in the final interval is the zero depth or its paired maximum depth. -/
theorem interval_depth_pair (d t v : Nat) (hl : d+4*t ≤ v) (hu : v ≤ d+14*t+1) :
    ∃ j,j ≤ 5*t ∧ (v=d+4*t+2*j ∨ v=d+4*t+2*j+1) := by
  refine ⟨(v-(d+4*t))/2,?_,?_⟩ <;> omega

def seedA2 : List Nat := [3,3,2,5,5,4,4,0,0,1,1,2]
def seedA3 : List Nat := [3,6,6,7,7,8,8,3,2,4,4,0,0,1,1,2,5,5]
def seedA4 : List Nat := [3,5,6,3,2,4,9,9,8,11,11,10,10,6,4,0,0,1,1,2,5,7,7,8]
def seedB8 : List Nat := [3,7,7,6,6,5,4,0,0,1,1,2,5,3,2,4]
def seedB9 : List Nat := [3,6,7,7,8,8,4,0,0,1,1,2,5,3,2,4,6,5]
def seedB10 : List Nat := [3,8,9,9,7,5,4,0,0,1,1,2,5,3,2,4,6,7,8,6]
def seedB11 : List Nat := [3,3,2,5,8,6,4,0,0,1,1,2,6,10,10,9,9,8,7,4,5,7]
def seedB12 : List Nat := [3,3,2,5,7,9,4,0,0,1,1,2,6,4,5,6,8,7,11,11,10,10,9,8]
def seedB13 : List Nat := [3,3,2,6,8,5,4,0,0,1,1,2,5,7,9,11,12,12,10,8,11,10,7,4,6,9]
def seedB14 : List Nat := [3,3,2,6,8,5,4,0,0,1,1,2,5,7,10,13,13,12,12,9,9,11,11,8,7,4,6,10]
def seedB15 : List Nat := [3,3,2,6,8,5,4,0,0,1,1,2,5,7,9,14,14,13,13,12,12,10,11,9,10,8,7,4,6,11]
def seedB16 : List Nat := [3,3,2,5,8,6,4,0,0,1,1,2,6,9,12,15,15,14,14,11,11,13,13,10,10,8,9,7,5,4,7,12]

theorem seedA2_valid : AnchoredCore 6 8 seedA2 := by constructor <;> decide
theorem seedA3_valid : AnchoredCore 9 12 seedA3 := by constructor <;> decide
theorem seedA4_valid : AnchoredCore 12 16 seedA4 := by constructor <;> decide
theorem seedB8_valid : AnchoredCore 8 8 seedB8 := by constructor <;> decide
theorem seedB9_valid : AnchoredCore 9 8 seedB9 := by constructor <;> decide
theorem seedB10_valid : AnchoredCore 10 8 seedB10 := by constructor <;> decide
theorem seedB11_valid : AnchoredCore 11 8 seedB11 := by constructor <;> decide
theorem seedB12_valid : AnchoredCore 12 8 seedB12 := by constructor <;> decide
theorem seedB13_valid : AnchoredCore 13 8 seedB13 := by constructor <;> decide
theorem seedB14_valid : AnchoredCore 14 8 seedB14 := by constructor <;> decide
theorem seedB15_valid : AnchoredCore 15 8 seedB15 := by constructor <;> decide
theorem seedB16_valid : AnchoredCore 16 8 seedB16 := by constructor <;> decide

theorem seedsA (r : Nat) (hr : 2 ≤ r ∧ r ≤ 4) : ∃ c,AnchoredCore (3*r) (4*r) c := by
  have he : r=2 ∨ r=3 ∨ r=4 := by omega
  rcases he with rfl|rfl|rfl
  · exact ⟨seedA2,seedA2_valid⟩
  · exact ⟨seedA3,seedA3_valid⟩
  · exact ⟨seedA4,seedA4_valid⟩

theorem seedsB (r : Nat) (hr : 8 ≤ r ∧ r ≤ 16) : ∃ c,AnchoredCore r 8 c := by
  have he : r=8 ∨ r=9 ∨ r=10 ∨ r=11 ∨ r=12 ∨ r=13 ∨ r=14 ∨ r=15 ∨ r=16 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨seedB8,seedB8_valid⟩
  · exact ⟨seedB9,seedB9_valid⟩
  · exact ⟨seedB10,seedB10_valid⟩
  · exact ⟨seedB11,seedB11_valid⟩
  · exact ⟨seedB12,seedB12_valid⟩
  · exact ⟨seedB13,seedB13_valid⟩
  · exact ⟨seedB14,seedB14_valid⟩
  · exact ⟨seedB15,seedB15_valid⟩
  · exact ⟨seedB16,seedB16_valid⟩

/-- Core-level Theorem A, including every integer in its advertised interval. -/
theorem theoremA_cores (s v : Nat) (hs : 2 ≤ s)
    (hl : 4*s-8*((s-2)/3) ≤ v) (hu : v ≤ 4*s+2*((s-2)/3)+1) :
    ∃ d c,AnchoredCore (3*s) d c ∧ (v=d ∨ v=d+1) := by
  let t := (s-2)/3
  let r := s-3*t
  have hr : 2 ≤ r ∧ r ≤ 4 := by dsimp only [r,t]; omega
  have hp : 3*r+9*t=3*s := by dsimp only [r,t]; omega
  have hlo : 4*r+4*t=4*s-8*t := by dsimp only [r,t]; omega
  have hhi : 4*r+14*t+1=4*s+2*t+1 := by dsimp only [r,t]; omega
  obtain ⟨c,hc⟩ := seedsA r hr
  obtain ⟨j,hj,hv⟩ := interval_depth_pair (4*r) t v (by rw [hlo]; exact hl) (by rw [hhi]; exact hu)
  obtain ⟨c',hc'⟩ := interval_cores (3*r) (4*r) c hc t j hj
  rw [hp] at hc'
  exact ⟨4*r+4*t+2*j,c',hc',hv⟩

/-- Core-level Theorem B for every p>=8, including every integer in its interval. -/
theorem theoremB_cores (p v : Nat) (hp : 8 ≤ p)
    (hl : 8+4*((p-8)/9) ≤ v) (hu : v ≤ 9+14*((p-8)/9)) :
    ∃ d c,AnchoredCore p d c ∧ (v=d ∨ v=d+1) := by
  let t := (p-8)/9
  let r := p-9*t
  have hr : 8 ≤ r ∧ r ≤ 16 := by dsimp only [r,t]; omega
  have he : r+9*t=p := by dsimp only [r,t]; omega
  obtain ⟨c,hc⟩ := seedsB r hr
  obtain ⟨j,hj,hv⟩ := interval_depth_pair 8 t v hl (by omega)
  obtain ⟨c',hc'⟩ := interval_cores r 8 c hc t j hj
  rw [he] at hc'
  exact ⟨8+4*t+2*j,c',hc',hv⟩

end GracefulBoundary.Variable
