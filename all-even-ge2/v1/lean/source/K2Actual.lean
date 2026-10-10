import TipFixed

namespace GracefulBoundary.K2Actual
open FullFixed

def core : List Nat := [1,0,0]

theorem core_valid : RootZeroTip.CorePacket 1 core := by
  constructor <;> decide

theorem core_tip (N : Nat) : (decode N false core)[2]? = some 0 := by rfl

theorem center_zero (n m : Nat) :
    ∃ f : SpiderVertex n m 2 → Nat,
      Graceful (spiderGraph n m 2) (n*2+m) f ∧ f .center=0 := by
  exact FullFixed.center_zero 1 n m (by decide)

theorem short_leaf_zero (n m : Nat) (a : Fin m) :
    ∃ f : SpiderVertex n m 2 → Nat,
      Graceful (spiderGraph n m 2) (n*2+m) f ∧ f (.leaf a)=0 := by
  exact FullFixed.short_leaf_zero 1 n m (by decide) a

theorem tip_zero (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃ f : SpiderVertex n m 2 → Nat,
      Graceful (spiderGraph n m 2) (n*2+m) f ∧
      f (.arm a ⟨1,by decide⟩)=0 := by
  exact FullFixed.supplied_tip_zero 1 n m (by decide) (by omega)
    core core_valid core_tip a

theorem support_max (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃ f : SpiderVertex n m 2 → Nat,
      Graceful (spiderGraph n m 2) (n*2+m) f ∧
      f (.arm a ⟨0,by decide⟩)=n*2+m := by
  obtain ⟨h,rfl⟩ : ∃h,n=h+1 := ⟨n-1,by omega⟩
  let g := residualLabel h m 2
  let Q := h*2+m
  let f := RootZeroTip.label Q 1 core g
  have hf := RootZeroTip.packet_attachment_graceful
    (spiderGraph h m 2) .center Q 1 core core_valid g
    (EvenResidual.residual_gracefulness h m 1 (by decide)) rfl
  have hmax : f (.inr ⟨0,by decide⟩)=Q+2 := by
    simp [f,RootZeroTip.label,RootZeroTip.armLabels,decode,core]
  have hgraph : RootZeroTip.graph (spiderGraph h m 2) .center 1 =
      FixedEven.graph (spiderGraph h m 2) .center 2 := by
    simpa only [show 2*1=2 by decide] using (FullFixed.root_zero_shell_graph h m 1)
  rw [hgraph] at hf
  simp only [show 2*1=2 by decide] at hf
  have size : Q+2=(h+1)*2+m := by dsimp [Q]; omega
  rw [size] at hf
  let f0 := fun v => f (FixedEven.Append.toV h m 2 v)
  have hf0 : Graceful (spiderGraph (h+1) m 2) ((h+1)*2+m) f0 :=
    FixedEven.Append.graceful_actual _ _ _ _ f hf
  let z : Fin (h+1) := ⟨h,by omega⟩
  have hz : f0 (.arm z ⟨0,by decide⟩)=(h+1)*2+m := by
    simpa only [f0,z,FixedEven.Append.toV,Nat.lt_irrefl,dite_false,size] using hmax
  exact ⟨fun v => f0 (NearTip.swapVertex a z v),
    NearTip.graceful_swap a z f0 hf0,
    by simpa only [NearTip.swapVertex,NearTip.swapIndex_first] using hz⟩

theorem support_zero (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃ f : SpiderVertex n m 2 → Nat,
      Graceful (spiderGraph n m 2) (n*2+m) f ∧
      f (.arm a ⟨0,by decide⟩)=0 := by
  obtain ⟨g,hg,hm⟩ := support_max n m hn a
  exact ⟨complementLabel (n*2+m) g,
    whole_graph_graceful_complement _ _ g hg,
    complement_maximum_zero _ g _ hm⟩

/-- Every actual named vertex has a graceful zero labeling. -/
theorem full_actual (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 2) :
    ∃ f : SpiderVertex n m 2 → Nat,
      Graceful (spiderGraph n m 2) (n*2+m) f ∧ f v=0 := by
  cases v with
  | center => exact center_zero n m
  | leaf a => exact short_leaf_zero n m a
  | arm a d =>
    by_cases hd : d.val=0
    · have heq : d=⟨0,by decide⟩ := Fin.ext hd
      rw [heq]
      exact support_zero n m hn a
    · have hdval : d.val=1 := by have hlt : d.val<2 := d.isLt; omega
      have heq : d=⟨1,by decide⟩ := Fin.ext hdval
      rw [heq]
      exact tip_zero n m hn a

theorem full_unique_zero (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 2) :
    ∃ f : SpiderVertex n m 2 → Nat,
      Graceful (spiderGraph n m 2) (n*2+m) f ∧
      f v=0 ∧ ∀ w, w≠v → 0<f w := by
  obtain ⟨f,hf,hz⟩ := full_actual n m hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have hne : f w≠0 := by
    intro h
    exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.K2Actual

#print axioms GracefulBoundary.K2Actual.core_valid
#print axioms GracefulBoundary.K2Actual.core_tip
#print axioms GracefulBoundary.K2Actual.center_zero
#print axioms GracefulBoundary.K2Actual.short_leaf_zero
#print axioms GracefulBoundary.K2Actual.tip_zero
#print axioms GracefulBoundary.K2Actual.support_max
#print axioms GracefulBoundary.K2Actual.support_zero
#print axioms GracefulBoundary.K2Actual.full_actual
#print axioms GracefulBoundary.K2Actual.full_unique_zero
