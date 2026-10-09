import AllOddDepth

namespace GracefulBoundary.AllOdd

theorem rooted_path_accounting (k : Nat) (hk : 19≤k) (hodd : k%2=1) :
    2*((k-3)/2)+3=k ∧ 4*((k-3)/2)+6=2*k := by omega

abbrev RootedVertices (p : Nat) (W : Type) :=
  GraftVertices (Fin (4*p+7)) W (Variable.boundaryCenter p)

noncomputable def rootedGraph {W F : Type} (p : Nat) (H : IndexedGraph W F) (root : W) :=
  graftGraph (pathGraph (4*p+6)) H (Variable.boundaryCenter p) root

/-- The inherited full-band Graceful interface covers every graceful tree and
    graphs satisfying that exact vertex/edge bijection contract. -/
theorem certificate_rooted_zero {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q p z q d : Nat) (hg : Graceful H Q g) (hroot : g root=0)
    (c : List Nat) (hc : FiniteAlpha.Certificate p z q c) (target : d=z ∨ d=q) :
    ∃ f : RootedVertices p W → Nat,
      Graceful (rootedGraph p H root) (4*p+6+Q) f ∧
      f (graftEmbed (Variable.boundaryCenter p) root
        (⟨2*p+3-d,by omega⟩ : Fin (4*p+7)))=0 := by
  rcases hc with ⟨_,_,_,_,generic,zero,maximal⟩
  rcases generic with ⟨length,labels,edges,alpha,midpoint⟩
  have hp := list_path_graceful (4*p+6) c labels edges
  have ha := list_path_alpha (4*p+6) (2*p+2) c length alpha
  have hcenter : pathLabel (4*p+6) c (Variable.boundaryCenter p)=2*p+2 := by
    change c[2*p+3]?.getD 0=2*p+2
    rw [midpoint]
    rfl
  have hz : pathLabel (4*p+6) c (⟨2*p+3-z,by omega⟩ : Fin (4*p+7))=0 := by
    simp [pathLabel,List.getD_eq_getElem?_getD,zero]
  have hm : pathLabel (4*p+6) c (⟨2*p+3-q,by omega⟩ : Fin (4*p+7))=4*p+6 := by
    simp [pathLabel,List.getD_eq_getElem?_getD,maximal]
  let f := graftLabel (Variable.boundaryCenter p) (pathLabel (4*p+6) c) g (2*p+2) Q
  have hf : Graceful (rootedGraph p H root) (4*p+6+Q) f :=
    graceful_graft (pathGraph (4*p+6)) H (Variable.boundaryCenter p) root
      (pathLabel (4*p+6) c) g (2*p+2) (4*p+6) Q hp hg hcenter hroot ha
  have gz := graft_zero_anchor (Variable.boundaryCenter p) root (pathLabel (4*p+6) c)
    g (2*p+2) Q hcenter hroot (⟨2*p+3-z,by omega⟩ : Fin (4*p+7)) hz
  have gm := graft_max_anchor (Variable.boundaryCenter p) root (pathLabel (4*p+6) c)
    g (2*p+2) (4*p+6) Q hcenter hroot (by omega)
    (⟨2*p+3-q,by omega⟩ : Fin (4*p+7)) hm
  rcases target with target | target
  · subst d
    exact ⟨f,hf,gz⟩
  · subst d
    refine ⟨fun v => 4*p+6+Q-f v,graceful_complement _ _ f hf,?_⟩
    change 4*p+6+Q-f (graftEmbed (Variable.boundaryCenter p) root
      (⟨2*p+3-q,by omega⟩ : Fin (4*p+7)))=0
    rw [show f (graftEmbed (Variable.boundaryCenter p) root
      (⟨2*p+3-q,by omega⟩ : Fin (4*p+7)))=4*p+6+Q from gm]
    exact Nat.sub_self _

theorem all_odd_rooted_zero {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q : Nat) (hg : Graceful H Q g) (hroot : g root=0)
    (d k : Nat) (hd : 2≤d) (hodd : k%2=1) (hk : cutoff d≤k) :
    ∃ f : RootedVertices ((k-3)/2) W → Nat,
      Graceful (rootedGraph ((k-3)/2) H root) (4*((k-3)/2)+6+Q) f ∧
      f (graftEmbed (Variable.boundaryCenter ((k-3)/2)) root
        (⟨2*((k-3)/2)+3-d,by omega⟩ : Fin (4*((k-3)/2)+7)))=0 := by
  obtain ⟨z,q,c,hc,target⟩ := odd_pair_certificate d k hd hodd hk
  exact certificate_rooted_zero H root g Q ((k-3)/2) z q d hg hroot c hc target

end GracefulBoundary.AllOdd
