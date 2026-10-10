import EvenShell
namespace GracefulBoundary.Even

/-- Finite path data required for transfer; no core or recurrence premise. -/
def Certificate (p z q : Nat) (c : List Nat) : Prop :=
  1 ≤ z ∧ z ≤ 2*p+4 ∧ 1 ≤ q ∧ q ≤ 2*p+4 ∧ GenericPathCertificate p c ∧
  c[2*p+4-z]?=some 0 ∧ c[2*p+4-q]?=some (4*p+8)

theorem first_arm (p z q h m : Nat) (c : List Nat) (hc : Certificate p z q c) :
    ∃ f : SpiderVertex (h+2) m (2*p+4) → Nat,
      Graceful (spiderGraph (h+2) m (2*p+4)) ((h+2)*(2*p+4)+m) f ∧
      f (.arm ⟨0,by omega⟩ ⟨z-1,by have := hc.2.1; omega⟩)=0 ∧
      f (.arm ⟨0,by omega⟩ ⟨q-1,by have := hc.2.2.2.1; omega⟩)=(h+2)*(2*p+4)+m := by
  rcases hc with ⟨hz,hzb,hq,hqb,hgeneric,hzero,hmax⟩
  rcases hgeneric with ⟨hlen,hv,he,ha,hmid⟩
  have hp := list_path_graceful (4*p+8) c hv he
  have halpha := list_path_alpha (4*p+8) (2*p+4) c hlen ha
  have hcenter : pathLabel (4*p+8) c (boundaryCenter p)=2*p+4 := by
    change c[2*p+4]?.getD 0=2*p+4
    rw [hmid]
    rfl
  have hzlabel : pathLabel (4*p+8) c ⟨2*p+4-z,by omega⟩=0 := by
    simp [pathLabel,List.getD_eq_getElem?_getD,hzero]
  have hmlabel : pathLabel (4*p+8) c ⟨2*p+4-q,by omega⟩=4*p+8 := by
    simp [pathLabel,List.getD_eq_getElem?_getD,hmax]
  let f := boundaryGraftLabel p h m c
  have hr : Graceful (spiderGraph h m (2*p+4)) (h*(2*p+4)+m) (residualLabel h m (2*p+4)) :=
    by
      have hr := EvenResidual.residual_gracefulness h m (p+2) (by omega)
      have hk : 2*(p+2)=2*p+4 := by omega
      rw [hk] at hr
      exact hr
  have hf : Graceful (boundaryGraftGraph p h m) (4*p+8+(h*(2*p+4)+m)) f :=
    graceful_graft (pathGraph (4*p+8)) (spiderGraph h m (2*p+4)) (boundaryCenter p) SpiderVertex.center
      (pathLabel (4*p+8) c) (residualLabel h m (2*p+4)) (2*p+4) (4*p+8) (h*(2*p+4)+m)
      hp hr hcenter rfl halpha
  have hg := graft_graceful_on_spider p h m _ f hf
  have gz := graft_zero_anchor (boundaryCenter p) SpiderVertex.center (pathLabel (4*p+8) c)
    (residualLabel h m (2*p+4)) (2*p+4) (h*(2*p+4)+m) hcenter rfl ⟨2*p+4-z,by omega⟩ hzlabel
  have gm := graft_max_anchor (boundaryCenter p) SpiderVertex.center (pathLabel (4*p+8) c)
    (residualLabel h m (2*p+4)) (2*p+4) (4*p+8) (h*(2*p+4)+m) hcenter rfl (by omega) ⟨2*p+4-q,by omega⟩ hmlabel
  have identify (d : Nat) (hd : 1≤d) (hb : d≤2*p+4) :
      spiderToGraft p h m (.arm ⟨0,by omega⟩ ⟨d-1,by omega⟩)=
      graftEmbed (boundaryCenter p) SpiderVertex.center (⟨2*p+4-d,by omega⟩ : Fin (4*p+9)) := by
    simp only [spiderToGraft,dite_true]
    have he : (⟨2*p+4-d,by omega⟩ : Fin (4*p+9))=(leftVertex p ⟨d-1,by omega⟩).val := by
      apply Fin.ext
      dsimp only [leftVertex]
      omega
    rw [he,embed_left]
  have hsize : 4*p+8+(h*(2*p+4)+m)=(h+2)*(2*p+4)+m := by simp only [Nat.add_mul]; omega
  rw [hsize] at hg gm
  refine ⟨fun v => f (spiderToGraft p h m v),hg,?_,?_⟩
  · dsimp only; rw [identify z hz hzb]; exact gz
  · dsimp only; rw [identify q hq hqb]; exact gm

/-- A supplied finite midpoint-alpha certificate transfers to every chosen arm,
    every n>=2 and m>=0, with separate zero labelings at both extreme depths. -/
theorem prescribed_zero (p z q n m : Nat) (c : List Nat) (hc : Certificate p z q c)
    (hn : 2 ≤ n) (a : Fin n) :
    (∃ f : SpiderVertex n m (2*p+4) → Nat,
      Graceful (spiderGraph n m (2*p+4)) (n*(2*p+4)+m) f ∧
      f (.arm a ⟨z-1,by have := hc.2.1; omega⟩)=0) ∧
    (∃ f : SpiderVertex n m (2*p+4) → Nat,
      Graceful (spiderGraph n m (2*p+4)) (n*(2*p+4)+m) f ∧
      f (.arm a ⟨q-1,by have := hc.2.2.2.1; omega⟩)=0) := by
  obtain ⟨h,rfl⟩ : ∃ h,n=h+2 := ⟨n-2,by omega⟩
  obtain ⟨f,hf,hzero,hmax⟩ := first_arm p z q h m c hc
  let b : Fin (h+2) := ⟨0,by omega⟩
  let g := fun v => f (swapVertex a b v)
  have hg : Graceful (spiderGraph (h+2) m (2*p+4)) ((h+2)*(2*p+4)+m) g := graceful_swap a b f hf
  have gz : g (.arm a ⟨z-1,by have := hc.2.1; omega⟩)=0 := by simpa only [g,swapVertex,swapIndex_first] using hzero
  have gm : g (.arm a ⟨q-1,by have := hc.2.2.2.1; omega⟩)=(h+2)*(2*p+4)+m := by simpa only [g,swapVertex,swapIndex_first] using hmax
  refine ⟨⟨g,hg,gz⟩,⟨fun v => (h+2)*(2*p+4)+m-g v,graceful_complement _ _ g hg,?_⟩⟩
  simp only [gm,Nat.sub_self]



open FixedDepth

theorem core_pair_to_certificate (p z q : Nat) (c : List Nat)
    (hc : CorePair p z q c) :
    Certificate p z q (completePath p c) := by
  have hz := complete_path_core_lookup p c (z-1) hc.boundary.2.1
    (by have := hc.zeroPositive; have := hc.zeroInside; omega)
  have hq := complete_path_core_lookup p c (q-1) hc.boundary.2.1
    (by have := hc.maxPositive; have := hc.maxInside; omega)
  rw [coreLabels_lookup,hc.zeroL] at hz
  rw [coreLabels_lookup,hc.zeroH] at hq
  have ho : ¬ (z-1)%2=0 := by have := hc.zeroEven; have := hc.zeroPositive; omega
  have he : (q-1)%2=0 := by have := hc.maxOdd; have := hc.maxPositive; omega
  simp only [ho,ite_false,Option.map_some] at hz
  simp only [he,ite_true,Option.map_some,Nat.sub_zero] at hq
  refine ⟨hc.zeroPositive,by have := hc.zeroInside; omega,hc.maxPositive,
    by have := hc.maxInside; omega,boundary_shell_bridge p c hc.boundary,?_,?_⟩
  · simpa only [show 2*p+3-(z-1)=2*p+4-z by
      have := hc.zeroPositive; have := hc.zeroInside; omega] using hz
  · simpa only [show 2*p+3-(q-1)=2*p+4-q by
      have := hc.maxPositive; have := hc.maxInside; omega] using hq

theorem core_pair_spider_transfer (p z q n m : Nat) (c : List Nat)
    (hc : CorePair p z q c) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m (2*p+4) → Nat,
      Graceful (spiderGraph n m (2*p+4)) (n*(2*p+4)+m) f ∧
      f (.arm a ⟨z-1,by have := hc.zeroInside; omega⟩)=0) ∧
    (∃ f : SpiderVertex n m (2*p+4) → Nat,
      Graceful (spiderGraph n m (2*p+4)) (n*(2*p+4)+m) f ∧
      f (.arm a ⟨q-1,by have := hc.maxInside; omega⟩)=0) := by
  exact prescribed_zero p z q n m (completePath p c)
    (core_pair_to_certificate p z q c hc) hn a


end GracefulBoundary.Even
