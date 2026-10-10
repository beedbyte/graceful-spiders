import UniformStep
namespace GracefulBoundary.EvenUniform
open FixedEven

theorem cuts_comm (A x y : Nat) : cuts A x y ↔ cuts A y x := by dsimp only [cuts]; omega

theorem residual_cuts (k m A : Nat) (f : Sum (Fin (2*k+1)) (Fin m) → Nat) (e : SpiderEdge 2 m k) :
    cuts A (f (CenterLeaves.Residual.toV k m ((spiderGraph 2 m k).source e)))
      (f (CenterLeaves.Residual.toV k m ((spiderGraph 2 m k).target e))) ↔
    cuts A (f ((CenterLeaves.graph k m).source (CenterLeaves.Residual.toE k m e)))
      (f ((CenterLeaves.graph k m).target (CenterLeaves.Residual.toE k m e))) := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    by_cases h0 : i.val=0
    · by_cases hd : d.val=0
      · simp only [spiderGraph,CenterLeaves.Residual.toV,CenterLeaves.Residual.toE,CenterLeaves.graph,h0,hd,ite_true]
        have he : (⟨k-1-0+1,by omega⟩ : Fin (2*k+1))=⟨k,by omega⟩ := by apply Fin.ext; dsimp only; omega
        rw [he]; exact cuts_comm _ _ _
      · simp only [spiderGraph,CenterLeaves.Residual.toV,CenterLeaves.Residual.toE,CenterLeaves.graph,h0,hd,ite_true,ite_false]
        have he : (⟨k-1-(d.val-1),by omega⟩ : Fin (2*k+1))=⟨k-1-d.val+1,by omega⟩ := by apply Fin.ext; dsimp only; omega
        rw [he]; exact cuts_comm _ _ _
    · by_cases hd : d.val=0
      · simp only [spiderGraph,CenterLeaves.Residual.toV,CenterLeaves.Residual.toE,CenterLeaves.graph,h0,hd,ite_true,ite_false]; rfl
      · simp only [spiderGraph,CenterLeaves.Residual.toV,CenterLeaves.Residual.toE,CenterLeaves.graph,h0,hd,ite_false]
        have he : (⟨k+1+(d.val-1),by omega⟩ : Fin (2*k+1))=⟨k+d.val,by omega⟩ := by apply Fin.ext; dsimp only; omega
        have ht : (⟨k+1+d.val,by omega⟩ : Fin (2*k+1))=⟨k+d.val+1,by omega⟩ := by apply Fin.ext; dsimp only; omega
        rw [he,ht]

theorem residual_alpha (k m A : Nat) (f : Sum (Fin (2*k+1)) (Fin m) → Nat)
    (ha : Alpha (CenterLeaves.graph k m) A f) :
    Alpha (spiderGraph 2 m k) A (fun v => f (CenterLeaves.Residual.toV k m v)) := by
  intro e
  exact (residual_cuts k m A f e).mpr (ha (CenterLeaves.Residual.toE k m e))

theorem alpha_path_to_actual_base (k : Nat) (hk : 2≤k) (g : Fin (2*k+1) → Nat)
    (hg : Graceful (pathGraph (2*k)) (2*k) g) (ha : Alpha (pathGraph (2*k)) k g)
    (hr : g ⟨k,by omega⟩=1) (hm : g ⟨k+1,by omega⟩=2*k) (hz : g ⟨k+2,by omega⟩=0) :
    ∃f : SpiderVertex 2 0 k → Nat, Graceful (spiderGraph 2 0 k) (2*k) f ∧ Alpha (spiderGraph 2 0 k) k f ∧
      f .center=1 ∧ f (.arm ⟨1,by omega⟩ ⟨0,by omega⟩)=2*k ∧ f (.arm ⟨1,by omega⟩ ⟨1,by omega⟩)=0 := by
  let f := emptySum g
  have hf : Graceful (CenterLeaves.graph k 0) (2*k) f := by
    constructor
    · exact empty_sum_band g 0 (2*k) hg.vertices
    · have hb := empty_sum_band (weight (pathGraph (2*k)) g) 1 (2*k) hg.edges
      have eq : weight (CenterLeaves.graph k 0) f=emptySum (weight (pathGraph (2*k)) g) := by
        funext e; cases e with
        | inl e => rfl
        | inr i => exact Fin.elim0 i
      rw [eq]; exact hb
  have af : Alpha (CenterLeaves.graph k 0) k f := by
    intro e; cases e with
    | inl e => exact ha e
    | inr i => exact Fin.elim0 i
  refine ⟨fun v => f (CenterLeaves.Residual.toV k 0 v),CenterLeaves.Residual.graceful_actual k 0 f hf,residual_alpha k 0 k f af,hr,?_,?_⟩
  · simpa only [CenterLeaves.Residual.toV,show (1:Nat)≠0 by omega,ite_false,f,emptySum,Nat.add_zero] using hm
  · simpa only [CenterLeaves.Residual.toV,show (1:Nat)≠0 by omega,ite_false,f,emptySum] using hz

end GracefulBoundary.EvenUniform
