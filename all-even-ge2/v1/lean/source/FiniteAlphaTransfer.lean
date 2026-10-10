import VariableSpider
namespace GracefulBoundary.FiniteAlpha

/-- Finite path data required for transfer; no core or recurrence premise. -/
def Certificate (p z q : Nat) (c : List Nat) : Prop :=
  1 ≤ z ∧ z ≤ 2*p+3 ∧ 1 ≤ q ∧ q ≤ 2*p+3 ∧ GenericPathCertificate p c ∧
  c[2*p+3-z]?=some 0 ∧ c[2*p+3-q]?=some (4*p+6)

theorem first_arm (p z q h m : Nat) (c : List Nat) (hc : Certificate p z q c) :
    ∃ f : SpiderVertex (h+2) m (2*p+3) → Nat,
      Graceful (spiderGraph (h+2) m (2*p+3)) ((h+2)*(2*p+3)+m) f ∧
      f (.arm ⟨0,by omega⟩ ⟨z-1,by have := hc.2.1; omega⟩)=0 ∧
      f (.arm ⟨0,by omega⟩ ⟨q-1,by have := hc.2.2.2.1; omega⟩)=(h+2)*(2*p+3)+m := by
  rcases hc with ⟨hz,hzb,hq,hqb,hgeneric,hzero,hmax⟩
  rcases hgeneric with ⟨hlen,hv,he,ha,hmid⟩
  have hp := list_path_graceful (4*p+6) c hv he
  have halpha := list_path_alpha (4*p+6) (2*p+2) c hlen ha
  have hcenter : pathLabel (4*p+6) c (Variable.boundaryCenter p)=2*p+2 := by
    change c[2*p+3]?.getD 0=2*p+2
    rw [hmid]
    rfl
  have hzlabel : pathLabel (4*p+6) c ⟨2*p+3-z,by omega⟩=0 := by
    simp [pathLabel,List.getD_eq_getElem?_getD,hzero]
  have hmlabel : pathLabel (4*p+6) c ⟨2*p+3-q,by omega⟩=4*p+6 := by
    simp [pathLabel,List.getD_eq_getElem?_getD,hmax]
  let f := Variable.boundaryGraftLabel p h m c
  have hr : Graceful (spiderGraph h m (2*p+3)) (h*(2*p+3)+m) (residualLabel h m (2*p+3)) :=
    residual_gracefulness h m (p+1)
  have hf : Graceful (Variable.boundaryGraftGraph p h m) (4*p+6+(h*(2*p+3)+m)) f :=
    graceful_graft (pathGraph (4*p+6)) (spiderGraph h m (2*p+3)) (Variable.boundaryCenter p) SpiderVertex.center
      (pathLabel (4*p+6) c) (residualLabel h m (2*p+3)) (2*p+2) (4*p+6) (h*(2*p+3)+m)
      hp hr hcenter rfl halpha
  have hg := Variable.graft_graceful_on_spider p h m _ f hf
  have gz := graft_zero_anchor (Variable.boundaryCenter p) SpiderVertex.center (pathLabel (4*p+6) c)
    (residualLabel h m (2*p+3)) (2*p+2) (h*(2*p+3)+m) hcenter rfl ⟨2*p+3-z,by omega⟩ hzlabel
  have gm := graft_max_anchor (Variable.boundaryCenter p) SpiderVertex.center (pathLabel (4*p+6) c)
    (residualLabel h m (2*p+3)) (2*p+2) (4*p+6) (h*(2*p+3)+m) hcenter rfl (by omega) ⟨2*p+3-q,by omega⟩ hmlabel
  have identify (d : Nat) (hd : 1≤d) (hb : d≤2*p+3) :
      Variable.spiderToGraft p h m (.arm ⟨0,by omega⟩ ⟨d-1,by omega⟩)=
      graftEmbed (Variable.boundaryCenter p) SpiderVertex.center (⟨2*p+3-d,by omega⟩ : Fin (4*p+7)) := by
    simp only [Variable.spiderToGraft,dite_true]
    have he : (⟨2*p+3-d,by omega⟩ : Fin (4*p+7))=(Variable.leftVertex p ⟨d-1,by omega⟩).val := by
      apply Fin.ext
      dsimp only [Variable.leftVertex]
      omega
    rw [he,Variable.embed_left]
  have hsize : 4*p+6+(h*(2*p+3)+m)=(h+2)*(2*p+3)+m := by simp only [Nat.add_mul]; omega
  rw [hsize] at hg gm
  refine ⟨fun v => f (Variable.spiderToGraft p h m v),hg,?_,?_⟩
  · dsimp only; rw [identify z hz hzb]; exact gz
  · dsimp only; rw [identify q hq hqb]; exact gm

/-- A supplied finite midpoint-alpha certificate transfers to every chosen arm,
    every n>=2 and m>=0, with separate zero labelings at both extreme depths. -/
theorem prescribed_zero (p z q n m : Nat) (c : List Nat) (hc : Certificate p z q c)
    (hn : 2 ≤ n) (a : Fin n) :
    (∃ f : SpiderVertex n m (2*p+3) → Nat,
      Graceful (spiderGraph n m (2*p+3)) (n*(2*p+3)+m) f ∧
      f (.arm a ⟨z-1,by have := hc.2.1; omega⟩)=0) ∧
    (∃ f : SpiderVertex n m (2*p+3) → Nat,
      Graceful (spiderGraph n m (2*p+3)) (n*(2*p+3)+m) f ∧
      f (.arm a ⟨q-1,by have := hc.2.2.2.1; omega⟩)=0) := by
  obtain ⟨h,rfl⟩ : ∃ h,n=h+2 := ⟨n-2,by omega⟩
  obtain ⟨f,hf,hzero,hmax⟩ := first_arm p z q h m c hc
  let b : Fin (h+2) := ⟨0,by omega⟩
  let g := fun v => f (swapVertex a b v)
  have hg : Graceful (spiderGraph (h+2) m (2*p+3)) ((h+2)*(2*p+3)+m) g := graceful_swap a b f hf
  have gz : g (.arm a ⟨z-1,by have := hc.2.1; omega⟩)=0 := by simpa only [g,swapVertex,swapIndex_first] using hzero
  have gm : g (.arm a ⟨q-1,by have := hc.2.2.2.1; omega⟩)=(h+2)*(2*p+3)+m := by simpa only [g,swapVertex,swapIndex_first] using hmax
  refine ⟨⟨g,hg,gz⟩,⟨fun v => (h+2)*(2*p+3)+m-g v,graceful_complement _ _ g hg,?_⟩⟩
  simp only [gm,Nat.sub_self]

end GracefulBoundary.FiniteAlpha
