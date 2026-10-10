import K4RootOne

namespace GracefulBoundary.K4Inventory

open K4RootOne

theorem base_arm_injective (n : Nat) (hn : 1≤n)
    (i j : Fin n) (d e : Fin 4)
    (h : base n (.arm i d)=base n (.arm j e)) : i=j ∧ d=e := by
  have hi := i.isLt
  have hj := j.isLt
  have hd := d.isLt
  have he := e.isLt
  have hboth : i.val=j.val ∧ d.val=e.val := by
    by_cases hi0 : i.val=0 <;> by_cases hj0 : j.val=0
    all_goals
      rcases (show d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 by omega) with hd0|hd1|hd2|hd3 <;>
      rcases (show e.val=0 ∨ e.val=1 ∨ e.val=2 ∨ e.val=3 by omega) with he0|he1|he2|he3 <;>
      simp_all [base] <;>
      omega
  exact ⟨Fin.ext hboth.1,Fin.ext hboth.2⟩

theorem base_vertex_band (n : Nat) (hn : 1≤n) :
    BandBijection (base n) 0 (4*n) := by
  constructor
  · intro v
    cases v with
    | center => simp [base]; omega
    | leaf j => exact Fin.elim0 j
    | arm i d =>
      have hi := i.isLt
      have hd := d.isLt
      by_cases hi0 : i.val=0
      all_goals
        rcases (show d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 by omega) with h0|h1|h2|h3 <;>
        simp_all [base] <;> omega
  · intro v w heq
    cases v with
    | center =>
      cases w with
      | center => rfl
      | leaf j => exact Fin.elim0 j
      | arm i d =>
        have hi := i.isLt
        have hd := d.isLt
        by_cases hi0 : i.val=0
        all_goals
          rcases (show d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 by omega) with h0|h1|h2|h3 <;>
          simp_all [base] <;> omega
    | leaf j => exact Fin.elim0 j
    | arm i d =>
      cases w with
      | center =>
        have hi := i.isLt
        have hd := d.isLt
        by_cases hi0 : i.val=0
        all_goals
          rcases (show d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 by omega) with h0|h1|h2|h3 <;>
          simp_all [base] <;> omega
      | leaf j => exact Fin.elim0 j
      | arm j e =>
        obtain ⟨hij,hde⟩ := base_arm_injective n hn i j d e heq
        subst j
        subst e
        rfl
  · intro x _ hx
    have hdiv := Nat.mod_add_div x 4
    rcases (show x%4=0 ∨ x%4=1 ∨ x%4=2 ∨ x%4=3 by omega) with h0|h1|h2|h3
    · by_cases hz : x=0
      · refine ⟨.arm ⟨0,by omega⟩ ⟨1,by decide⟩,?_⟩
        simp [base,hz]
      by_cases hm : x=4*n
      · refine ⟨.arm ⟨0,by omega⟩ ⟨0,by decide⟩,?_⟩
        simp [base,hm]
      have hi : x/4<n := by omega
      have hip : x/4≠0 := by omega
      refine ⟨.arm ⟨x/4,hi⟩ ⟨1,by decide⟩,?_⟩
      simp [base,hip]
      omega
    · by_cases hz : x=1
      · exact ⟨.center,by simp [base,hz]⟩
      have hi : n-x/4<n := by omega
      have hip : n-x/4≠0 := by omega
      refine ⟨.arm ⟨n-x/4,hi⟩ ⟨0,by decide⟩,?_⟩
      simp [base,hip]
      omega
    · have hi : n-1-x/4<n := by omega
      refine ⟨.arm ⟨n-1-x/4,hi⟩ ⟨2,by decide⟩,?_⟩
      simp [base] <;> split <;> omega
    · have hi : x/4<n := by omega
      refine ⟨.arm ⟨x/4,hi⟩ ⟨3,by decide⟩,?_⟩
      simp [base] <;> split <;> omega

def oldLabel (n : Nat) : SpiderVertex n 0 2 → Nat := residualLabel n 0 2

def oddWeight (n x : Nat) : Nat := distance (4*n) (4*x+1)

def edgeCode (n : Nat) : SpiderEdge n 0 4 →
    Sum (SpiderEdge n 0 2) (SpiderVertex n 0 2)
  | .leaf j => Fin.elim0 j
  | .arm i d =>
    if i.val=0 then
      if d.val=0 then .inr .center
      else if d.val=1 then .inl (.arm i ⟨0,by decide⟩)
      else if d.val=2 then .inl (.arm i ⟨1,by decide⟩)
      else .inr (.arm i ⟨1,by decide⟩)
    else
      if d.val=0 then .inl (.arm i ⟨0,by decide⟩)
      else if d.val=1 then .inr (.arm i ⟨0,by decide⟩)
      else if d.val=2 then .inl (.arm i ⟨1,by decide⟩)
      else .inr (.arm i ⟨1,by decide⟩)

private theorem number_s0 (n : Nat) (hn : 1≤n) :
    distance 1 (4*n) = distance (4*n) (4*0+1) := by unfold distance; omega
private theorem number_s1 (n : Nat) (hn : 1≤n) :
    distance (4*n) 0 = 2*distance 0 (n*2) := by unfold distance; omega
private theorem number_s2 (n : Nat) (hn : 1≤n) :
    distance 0 (4*n-2) = 2*distance (n*2) 1 := by unfold distance; omega
private theorem number_s3 (n : Nat) (hn : 1≤n) :
    distance (4*n-2) 3 = distance (4*n) (4*1+1) := by unfold distance; omega
private theorem number_o0 (n i : Nat) (hi : i<n) :
    distance 1 (4*(n-i)+1) = 2*distance 0 ((n-i)*2) := by unfold distance; omega
private theorem number_o1 (n i : Nat) (hi : i<n) :
    distance (4*(n-i)+1) (4*i) = distance (4*n) (4*((n-i)*2)+1) := by unfold distance; omega
private theorem number_o2 (n i : Nat) (hi : i<n) :
    distance (4*i) (4*(n-i)-2) = 2*distance ((n-i)*2) (i*2+1) := by unfold distance; omega
private theorem number_o3 (n i : Nat) (hi : i<n) :
    distance (4*(n-i)-2) (4*i+3) = distance (4*n) (4*(i*2+1)+1) := by unfold distance; omega

theorem edge_code_weight (n : Nat) (hn : 1≤n) (e : SpiderEdge n 0 4) :
    weight (spiderGraph n 0 4) (base n) e =
      match edgeCode n e with
      | .inl a => 2 * weight (spiderGraph n 0 2) (oldLabel n) a
      | .inr v => oddWeight n (oldLabel n v) := by
  cases e with
  | leaf j => exact Fin.elim0 j
  | arm i d =>
    have hi := i.isLt
    have hd := d.isLt
    by_cases hi0 : i.val=0
    · have ieq : i=⟨0,by omega⟩ := Fin.ext hi0
      rw [ieq]
      rcases (show d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 by omega) with h0|h1|h2|h3
      · have deq : d=⟨0,by decide⟩ := Fin.ext h0
        rw [deq]
        simpa [edgeCode,weight,spiderGraph,base,oldLabel,residualLabel,oddWeight] using number_s0 n hn
      · have deq : d=⟨1,by decide⟩ := Fin.ext h1
        rw [deq]
        simpa [edgeCode,weight,spiderGraph,base,oldLabel,residualLabel,oddWeight] using number_s1 n hn
      · have deq : d=⟨2,by decide⟩ := Fin.ext h2
        rw [deq]
        simpa [edgeCode,weight,spiderGraph,base,oldLabel,residualLabel,oddWeight] using number_s2 n hn
      · have deq : d=⟨3,by decide⟩ := Fin.ext h3
        rw [deq]
        simpa [edgeCode,weight,spiderGraph,base,oldLabel,residualLabel,oddWeight,
          show (3 : Fin 4).val=3 by decide] using number_s3 n hn
    · rcases (show d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 by omega) with h0|h1|h2|h3
      · have deq : d=⟨0,by decide⟩ := Fin.ext h0
        rw [deq]
        simpa [edgeCode,weight,spiderGraph,base,oldLabel,residualLabel,oddWeight,hi0] using number_o0 n i.val hi
      · have deq : d=⟨1,by decide⟩ := Fin.ext h1
        rw [deq]
        simpa [edgeCode,weight,spiderGraph,base,oldLabel,residualLabel,oddWeight,hi0] using number_o1 n i.val hi
      · have deq : d=⟨2,by decide⟩ := Fin.ext h2
        rw [deq]
        simpa [edgeCode,weight,spiderGraph,base,oldLabel,residualLabel,oddWeight,hi0] using number_o2 n i.val hi
      · have deq : d=⟨3,by decide⟩ := Fin.ext h3
        rw [deq]
        simpa [edgeCode,weight,spiderGraph,base,oldLabel,residualLabel,oddWeight,hi0,
          show (3 : Fin 4).val=3 by decide] using number_o3 n i.val hi

def evenEdge (n : Nat) : SpiderEdge n 0 2 → SpiderEdge n 0 4
  | .leaf j => Fin.elim0 j
  | .arm i d =>
    if i.val=0 then
      if d.val=0 then .arm i ⟨1,by decide⟩ else .arm i ⟨2,by decide⟩
    else
      if d.val=0 then .arm i ⟨0,by decide⟩ else .arm i ⟨2,by decide⟩

def oddEdge (n : Nat) (hn : 1≤n) : SpiderVertex n 0 2 → SpiderEdge n 0 4
  | .center => .arm ⟨0,by omega⟩ ⟨0,by decide⟩
  | .leaf j => Fin.elim0 j
  | .arm i d =>
    if i.val=0 then .arm i ⟨3,by decide⟩
    else if d.val=0 then .arm i ⟨1,by decide⟩
    else .arm i ⟨3,by decide⟩

def decodeEdge (n : Nat) (hn : 1≤n) :
    Sum (SpiderEdge n 0 2) (SpiderVertex n 0 2) → SpiderEdge n 0 4
  | .inl e => evenEdge n e
  | .inr v => oddEdge n hn v

theorem decode_code (n : Nat) (hn : 1≤n) (e : SpiderEdge n 0 4) :
    decodeEdge n hn (edgeCode n e)=e := by
  cases e with
  | leaf j => exact Fin.elim0 j
  | arm i d =>
    have hd := d.isLt
    by_cases hi0 : i.val=0
    all_goals
      rcases (show d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 by omega) with h0|h1|h2|h3 <;>
      simp_all [decodeEdge,edgeCode,evenEdge,oddEdge] <;>
      apply Fin.ext <;> simp_all <;> decide

theorem code_injective (n : Nat) (hn : 1≤n) : Function.Injective (edgeCode n) := by
  intro e f hef
  calc
    e = decodeEdge n hn (edgeCode n e) := (decode_code n hn e).symm
    _ = decodeEdge n hn (edgeCode n f) := congrArg _ hef
    _ = f := decode_code n hn f

theorem code_even (n : Nat) (_hn : 1≤n) (e : SpiderEdge n 0 2) :
    edgeCode n (evenEdge n e)=.inl e := by
  cases e with
  | leaf j => exact Fin.elim0 j
  | arm i d =>
    have hd := d.isLt
    by_cases hi0 : i.val=0
    all_goals
      rcases (show d.val=0 ∨ d.val=1 by omega) with h0|h1 <;>
      simp_all [edgeCode,evenEdge] <;>
      apply Fin.ext <;> simp_all

theorem code_odd (n : Nat) (hn : 1≤n) (v : SpiderVertex n 0 2)
    (hnot : v ≠ .arm ⟨0,by omega⟩ ⟨0,by decide⟩) :
    edgeCode n (oddEdge n hn v)=.inr v := by
  cases v with
  | center => simp [edgeCode,oddEdge]
  | leaf j => exact Fin.elim0 j
  | arm i d =>
    have hd := d.isLt
    by_cases hi0 : i.val=0
    · rcases (show d.val=0 ∨ d.val=1 by omega) with h0|h1
      · have ieq : i=⟨0,by omega⟩ := Fin.ext hi0
        have deq : d=⟨0,by decide⟩ := Fin.ext h0
        exact False.elim (hnot (by rw [ieq,deq]))
      · have deq : d=⟨1,by decide⟩ := Fin.ext h1
        rw [deq]
        simp [edgeCode,oddEdge,hi0, show (3 : Fin 4).val=3 by decide]
    · rcases (show d.val=0 ∨ d.val=1 by omega) with h0|h1
      · simp_all [edgeCode,oddEdge]
      · have deq : d=⟨1,by decide⟩ := Fin.ext h1
        rw [deq]
        simp [edgeCode,oddEdge,hi0, show (3 : Fin 4).val=3 by decide]

theorem odd_bounds (n x : Nat) (hn : 1≤n) (hx : x<2*n) :
    1≤oddWeight n x ∧ oddWeight n x≤4*n-1 ∧ oddWeight n x%2=1 := by
  unfold oddWeight distance
  omega

theorem odd_injective (n x y : Nat) (_hn : 1≤n)
    (_hx : x<2*n) (_hy : y<2*n)
    (he : oddWeight n x=oddWeight n y) : x=y := by
  unfold oddWeight distance at he
  omega

theorem odd_onto (n y : Nat) (hn : 1≤n)
    (_hy : 1≤y) (hyTop : y≤4*n) (hodd : y%2=1) :
    ∃ x, x<2*n ∧ oddWeight n x=y := by
  have hdiv := Nat.mod_add_div y 4
  rcases (show y%4=1 ∨ y%4=3 by omega) with h1|h3
  · let x := n+(y-1)/4
    refine ⟨x,by dsimp [x]; omega,?_⟩
    unfold oddWeight distance
    dsimp [x]
    omega
  · let x := (4*n-1-y)/4
    refine ⟨x,by dsimp [x]; omega,?_⟩
    unfold oddWeight distance
    dsimp [x]
    omega

theorem code_ne_exception (n : Nat) (hn : 1≤n) (e : SpiderEdge n 0 4) :
    edgeCode n e ≠ .inr (.arm ⟨0,by omega⟩ ⟨0,by decide⟩) := by
  cases e with
  | leaf j => exact Fin.elim0 j
  | arm i d =>
    have hd := d.isLt
    by_cases hi0 : i.val=0
    all_goals
      rcases (show d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 by omega) with h0|h1|h2|h3 <;>
      simp_all [edgeCode] <;>
      (intro he; exact hi0 (congrArg Fin.val he))

theorem old_graceful (n : Nat) :
    Graceful (spiderGraph n 0 2) (2*n) (oldLabel n) := by
  simpa [oldLabel,Nat.mul_comm] using
    EvenResidual.residual_gracefulness n 0 1 (by decide)

theorem old_exception_max (n : Nat) (hn : 1≤n) :
    oldLabel n (.arm ⟨0,by omega⟩ ⟨0,by decide⟩)=2*n := by
  simp [oldLabel,residualLabel]
  omega

theorem coded_odd_lt (n : Nat) (hn : 1≤n) (e : SpiderEdge n 0 4)
    (v : SpiderVertex n 0 2) (hc : edgeCode n e=.inr v) :
    oldLabel n v < 2*n := by
  have hg := old_graceful n
  have hle := (hg.vertices.bounds v).2
  by_cases hlt : oldLabel n v < 2*n
  · exact hlt
  exfalso
  have heq : oldLabel n v=2*n := by omega
  have hv : v = (.arm ⟨0,by omega⟩ ⟨0,by decide⟩ : SpiderVertex n 0 2) :=
    hg.vertices.injective v _ (heq.trans (old_exception_max n hn).symm)
  exact code_ne_exception n hn e (by rw [hc,hv])

theorem base_edge_band (n : Nat) (hn : 1≤n) :
    BandBijection (weight (spiderGraph n 0 4) (base n)) 1 (4*n) := by
  have hg := old_graceful n
  constructor
  · intro e
    rw [edge_code_weight n hn e]
    cases hc : edgeCode n e with
    | inl a =>
      change 1≤2*weight (spiderGraph n 0 2) (oldLabel n) a ∧
        2*weight (spiderGraph n 0 2) (oldLabel n) a≤4*n
      have hb := hg.edges.bounds a
      constructor <;> omega
    | inr v =>
      change 1≤oddWeight n (oldLabel n v) ∧ oddWeight n (oldLabel n v)≤4*n
      have hv := coded_odd_lt n hn e v hc
      have hb := odd_bounds n (oldLabel n v) hn hv
      constructor <;> omega
  · intro e f heq
    have hw := heq
    rw [edge_code_weight n hn e,edge_code_weight n hn f] at hw
    cases hce : edgeCode n e with
    | inl a =>
      cases hcf : edgeCode n f with
      | inl b =>
        simp only [hce,hcf] at hw
        have hweight := Nat.eq_of_mul_eq_mul_left (show 0<2 by decide) hw
        have hab : a=b := hg.edges.injective a b hweight
        apply code_injective n hn
        rw [hce,hcf,hab]
      | inr v =>
        simp only [hce,hcf] at hw
        have hv := coded_odd_lt n hn f v hcf
        have hp := (odd_bounds n (oldLabel n v) hn hv).2.2
        have contradiction : (2*weight (spiderGraph n 0 2) (oldLabel n) a)%2=1 := by
          rw [hw]
          exact hp
        omega
    | inr v =>
      cases hcf : edgeCode n f with
      | inl b =>
        simp only [hce,hcf] at hw
        have hv := coded_odd_lt n hn e v hce
        have hp := (odd_bounds n (oldLabel n v) hn hv).2.2
        have contradiction : (2*weight (spiderGraph n 0 2) (oldLabel n) b)%2=1 := by
          rw [←hw]
          exact hp
        omega
      | inr w =>
        simp only [hce,hcf] at hw
        have hv := coded_odd_lt n hn e v hce
        have hwlt := coded_odd_lt n hn f w hcf
        have hlabel : oldLabel n v=oldLabel n w :=
          odd_injective n _ _ hn hv hwlt hw
        have hvw : v=w := hg.vertices.injective v w hlabel
        apply code_injective n hn
        rw [hce,hcf,hvw]
  · intro x hlo hhi
    by_cases heven : x%2=0
    · have hlow : 1≤x/2 := by omega
      have htop : x/2≤2*n := by omega
      obtain ⟨e,he⟩ := hg.edges.onto (x/2) hlow htop
      refine ⟨evenEdge n e,?_⟩
      rw [edge_code_weight n hn,code_even n hn e]
      simp only
      omega
    · have hodd : x%2=1 := by omega
      obtain ⟨y,hy,hyw⟩ := odd_onto n x hn hlo hhi hodd
      obtain ⟨v,hv⟩ := hg.vertices.onto y (by omega) (by omega)
      have hnot : v ≠ (.arm ⟨0,by omega⟩ ⟨0,by decide⟩ : SpiderVertex n 0 2) := by
        intro h
        rw [h,old_exception_max n hn] at hv
        omega
      refine ⟨oddEdge n hn v,?_⟩
      rw [edge_code_weight n hn,code_odd n hn v hnot]
      simpa only using (hv.symm ▸ hyw)

theorem base_graceful (n : Nat) (hn : 1≤n) :
    Graceful (spiderGraph n 0 4) (4*n) (base n) :=
  ⟨base_vertex_band n hn,base_edge_band n hn⟩

theorem base_gracefulness : K4RootOne.BaseGracefulness := by
  intro n hn
  exact base_graceful n hn
end GracefulBoundary.K4Inventory

#print axioms GracefulBoundary.K4Inventory.base_vertex_band
#print axioms GracefulBoundary.K4Inventory.edge_code_weight
#print axioms GracefulBoundary.K4Inventory.base_edge_band
#print axioms GracefulBoundary.K4Inventory.base_gracefulness
