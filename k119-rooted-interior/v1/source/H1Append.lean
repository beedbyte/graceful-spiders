import TaggedDecode
namespace GracefulBoundary.H1Append

def width (p : Nat) := 2*p+3
def next (p : Nat) := 4*p+6

structure State (p : Nat) (x : List Nat) : Prop where
  length : x.length=4*p+7
  high : (highs x).Perm (List.range (2*p+4))
  low : (lows x).Perm (List.range (2*p+3))
  sums : (edgeSums x).Perm (List.range (4*p+6))
  midpoint : x[2*p+3]?=some (2*p+2)
  start4 : x.take 4=[1,0,0,2]
  terminal : x.getLast?=some (2*p+2)

/-- The exact scaled old whole-arm core contract still requiring an explicit
    all-p construction theorem. This structure is not an axiom. -/
structure Tail (p : Nat) (z : List Nat) : Prop where
  length : z.length=12*p+24
  low : (highs z).Perm (List.range' (2*p+3) (6*p+12))
  high : (lows z).Perm (List.range' (2*p+4) (6*p+12))
  sums : (edgeSums z).Perm (List.range' (4*p+7) (12*p+23))
  first : z.head?=some (2*p+4)
  terminal : z.getLast?=some (8*p+14)
  midpoint : z[4*p+8]?=some (8*p+14)

theorem band_join (a b : Nat) :
    (List.range a ++ List.range' a b).Perm (List.range (a+b)) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_range,count_band]
  repeat (any_goals split)
  all_goals omega

theorem sum_join (p : Nat) :
    (List.range (4*p+6) ++ (4*p+6)::List.range' (4*p+7) (12*p+23)).Perm
      (List.range (16*p+30)) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_cons,List.count_range,count_band,Nat.beq_eq_true_eq]
  repeat (any_goals split)
  all_goals omega

theorem append_state (p : Nat) (x z : List Nat) (hx : State p x) (hz : Tail p z) :
    State (next p) (x++z) := by
  have odd : ¬x.length%2=0 := by rw [hx.length]; omega
  have high := hx.high.append hz.high
  have low := hx.low.append hz.low
  have eh := band_join (2*p+4) (6*p+12)
  have el := band_join (2*p+3) (6*p+12)
  have hedge : edgeSums (x++z)=edgeSums x ++ (4*p+6)::edgeSums z := by
    obtain ⟨zs,he⟩ := List.head?_eq_some_iff.mp hz.first
    rw [he,edgeSums_join x (2*p+2) (2*p+4) zs hx.terminal]
    congr 2
    omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [List.length_append,hx.length,hz.length,next]; omega
  · rw [highs_append]; simp only [odd,ite_false]
    simpa only [next,show 2*p+4+(6*p+12)=2*(4*p+6)+4 by omega] using high.trans eh
  · rw [lows_append]; simp only [odd,ite_false]
    simpa only [next,show 2*p+3+(6*p+12)=2*(4*p+6)+3 by omega] using low.trans el
  · rw [hedge]
    have hs := hx.sums.append (hz.sums.cons (4*p+6))
    simpa only [next,show 4*(4*p+6)+6=16*p+30 by omega] using hs.trans (sum_join p)
  · rw [List.getElem?_append_right (by rw [hx.length]; simp only [next]; omega),hx.length]
    simpa only [next,show 2*(4*p+6)+3-(4*p+7)=4*p+8 by omega,
      show 2*(4*p+6)+2=8*p+14 by omega] using hz.midpoint
  · rw [List.take_append_of_le_length (by rw [hx.length]; omega)]
    exact hx.start4
  · rw [List.getLast?_append,hz.terminal]
    change some (8*p+14)=some (2*(4*p+6)+2)
    congr 1 <;> omega

theorem lookup_prefix (p : Nat) (x : List Nat) (hx : State p x) :
    x[1]?=some 0 ∧ x[2]?=some 0 := by
  have h1 := congrArg (fun z : List Nat => z[1]?) hx.start4
  have h2 := congrArg (fun z : List Nat => z[2]?) hx.start4
  simpa using And.intro h1 h2

theorem certificate (p : Nat) (x : List Nat) (hx : State p x) :
    FiniteAlpha.Certificate p (2*p+2) (2*p+1) (coreLabels (4*p+6) x) := by
  obtain ⟨hz,hm⟩ := lookup_prefix p x hx
  have generic := WholeTagged.whole_path_certificate p x (by have := hx.length; omega)
    hx.high hx.low hx.sums hx.midpoint
  refine ⟨by omega,by omega,by omega,by omega,generic,?_,?_⟩
  · rw [show 2*p+3-(2*p+2)=1 by omega,coreLabels_lookup,hz]
    simp
  · rw [show 2*p+3-(2*p+1)=2 by omega,coreLabels_lookup,hm]
    simp

def level (p : Nat) : Nat → Nat
  | 0 => p
  | t+1 => next (level p t)

theorem level_closed (p t : Nat) : level p t+2=(p+2)*4^t := by
  induction t with
  | zero => simp [level]
  | succ t ih =>
    rw [Nat.pow_succ,←Nat.mul_assoc]
    simp only [level,next]
    omega

theorem width_closed (p t : Nat) : 2*level p t+4=(2*p+4)*4^t := by
  calc
    2*level p t+4=2*(level p t+2) := by omega
    _ = 2*((p+2)*4^t) := by rw [level_closed]
    _ = (2*p+4)*4^t := by rw [←Nat.mul_assoc]; congr 1

def family (tail : Nat → List Nat) (p : Nat) (x : List Nat) : Nat → List Nat
  | 0 => x
  | t+1 => family tail p x t ++ tail (level p t)

/-- Universal conditional iteration. The all-p tail premise remains visible. -/
theorem family_state (tail : Nat → List Nat) (ht : ∀ p,Tail p (tail p))
    (p : Nat) (x : List Nat) (hx : State p x) (t : Nat) :
    State (level p t) (family tail p x t) := by
  induction t with
  | zero => exact hx
  | succ t ih => exact append_state _ _ _ ih (ht _)

theorem actual_conditional (tail : Nat → List Nat) (ht : ∀ p,Tail p (tail p))
    (p : Nat) (x : List Nat) (hx : State p x) (t n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m (2*level p t+3) → Nat,
      Graceful (spiderGraph n m (2*level p t+3)) (n*(2*level p t+3)+m) f ∧
      f (.arm a ⟨2*level p t+1,by omega⟩)=0) ∧
    (∃ f : SpiderVertex n m (2*level p t+3) → Nat,
      Graceful (spiderGraph n m (2*level p t+3)) (n*(2*level p t+3)+m) f ∧
      f (.arm a ⟨2*level p t,by omega⟩)=0) := by
  have hc := certificate (level p t) _ (family_state tail ht p x hx t)
  simpa only [show 2*level p t+2-1=2*level p t+1 by omega,
    show 2*level p t+1-1=2*level p t by omega] using
    FiniteAlpha.prescribed_zero (level p t) (2*level p t+2) (2*level p t+1) n m _ hc hn a

def seed3 : List Nat := [1,0,0,2,3,1,2]
def seed7 : List Nat := [1,0,0,2,4,5,7,6,5,3,2,1,3,4,6]
def seed17 : List Nat := [1,0,0,2,3,1,2,4,4,3,6,7,9,10,12,13,15,16,17,15,14,12,11,9,8,6,5,5,7,8,10,11,13,14,16]
set_option maxRecDepth 8192 in
theorem seed3_state : State 0 seed3 := by constructor <;> decide
set_option maxRecDepth 8192 in
theorem seed7_state : State 2 seed7 := by constructor <;> decide
set_option maxRecDepth 8192 in
theorem seed17_state : State 7 seed17 := by constructor <;> decide

def permutationValue (s i : Nat) : Nat :=
  if i<2*s then (if i%2=0 then 1+3*(i/2) else 3*s-3-3*(i/2))
  else if (i-2*s)%2=0 then 3*s-1-3*((i-2*s)/2) else 2+3*((i-2*s)/2)
def halfCore (s : Nat) : List Nat :=
  (List.range (3*s)).map (fun i => if i%2=0 then permutationValue s i else 3*s-1-permutationValue s i)
def concreteCore (s : Nat) : List Nat :=
  halfCore s ++ (halfCore s).reverse.map (fun v => 3*s-1-v)
def concreteTail (p : Nat) : List Nat :=
  ((concreteCore (2*p+4)).zipIdx).map (fun vi => 2*p+3+vi.1+vi.2%2)
/-- The remaining formal obligation, not a proved theorem or an axiom. -/
def ConcreteTailInventory : Prop := ∀ p,Tail p (concreteTail p)

theorem concrete_three_bases_if (h : ConcreteTailInventory) (t : Nat) :
    State (level 0 t) (family concreteTail 0 seed3 t) ∧
    State (level 2 t) (family concreteTail 2 seed7 t) ∧
    State (level 7 t) (family concreteTail 7 seed17 t) := by
  exact ⟨family_state _ h _ _ seed3_state _,family_state _ h _ _ seed7_state _,
    family_state _ h _ _ seed17_state _⟩

def branchSeed (p : Nat) : List Nat :=
  if p=0 then seed3 else if p=2 then seed7 else seed17

theorem branchSeed_state (p : Nat) (hp : p=0 ∨ p=2 ∨ p=7) : State p (branchSeed p) := by
  rcases hp with rfl|rfl|rfl
  · exact seed3_state
  · exact seed7_state
  · exact seed17_state

/-- All t,n,m and every actual named arm, still conditional on the displayed
    concrete all-p tail inventory. No finite tail checks discharge h. -/
theorem three_branches_actual_if (h : ConcreteTailInventory) (p : Nat)
    (hp : p=0 ∨ p=2 ∨ p=7) (t n m d : Nat) (hn : 2≤n) (a : Fin n)
    (hd : d=2*level p t+1 ∨ d=2*level p t+2) :
    ∃ (hlt : d-1<2*level p t+3) (f : SpiderVertex n m (2*level p t+3) → Nat),
      Graceful (spiderGraph n m (2*level p t+3)) (n*(2*level p t+3)+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 := by
  have both := actual_conditional concreteTail h p (branchSeed p) (branchSeed_state p hp) t n m hn a
  rcases hd with rfl|rfl
  · obtain ⟨f,hf,hz⟩ := both.2
    exact ⟨by omega,f,hf,by simpa only [show 2*level p t+1-1=2*level p t by omega] using hz⟩
  · obtain ⟨f,hf,hz⟩ := both.1
    exact ⟨by omega,f,hf,by simpa only [show 2*level p t+2-1=2*level p t+1 by omega] using hz⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem concreteTail0_control : Tail 0 (concreteTail 0) := by constructor <;> decide
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem concreteTail2_control : Tail 2 (concreteTail 2) := by constructor <;> decide
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem concreteTail7_control : Tail 7 (concreteTail 7) := by constructor <;> decide

end GracefulBoundary.H1Append
