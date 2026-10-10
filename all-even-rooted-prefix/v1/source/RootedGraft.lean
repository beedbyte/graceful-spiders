import K71Full

namespace GracefulBoundary.Rooted71

def midpoint : Fin 143 := ⟨71,by decide⟩

def leftPoint (d : Nat) (hd : 1≤d ∧ d≤70) : Fin 143 := ⟨71-d,by omega⟩
def rightPoint (d : Nat) (hd : 1≤d ∧ d≤70) : Fin 143 := ⟨71+d,by omega⟩

theorem graft_extreme {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q : Nat) (hg : Graceful H Q g) (hroot : g root=0)
    (w : List Nat) (hw : GenericPathCertificate 34 w) (i : Fin 143)
    (hextreme : w[i.val]?=some 0 ∨ w[i.val]?=some 142) :
    ∃ f : GraftVertices (Fin 143) W midpoint → Nat,
      Graceful (graftGraph (pathGraph 142) H midpoint root) (142+Q) f ∧
      f (graftEmbed midpoint root i)=0 := by
  rcases hw with ⟨hlen,hv,he,ha,hm⟩
  let pf := pathLabel 142 w
  have hpath : Graceful (pathGraph 142) 142 pf := list_path_graceful 142 w hv he
  have hcut : Alpha (pathGraph 142) 70 pf := list_path_alpha 142 70 w hlen ha
  have hcenter : pf midpoint=70 := by
    change w.getD 71 0=70
    rw [List.getD_eq_getElem?_getD,hm]
    rfl
  let label := graftLabel midpoint pf g 70 Q
  have hgraceful : Graceful (graftGraph (pathGraph 142) H midpoint root)
      (142+Q) label :=
    graceful_graft (pathGraph 142) H midpoint root pf g 70 142 Q
      hpath hg hcenter hroot hcut
  have htarget : label (graftEmbed midpoint root i)=alphaShift 70 Q (pf i) :=
    graftLabel_embed midpoint root pf g 70 Q hcenter hroot i
  rcases hextreme with hz|hmx
  · have hp : pf i=0 := by
      change w.getD i.val 0=0
      rw [List.getD_eq_getElem?_getD,hz]
      rfl
    refine ⟨label,hgraceful,?_⟩
    rw [htarget,hp]
    simp [alphaShift]
  · have hp : pf i=142 := by
      change w.getD i.val 0=142
      rw [List.getD_eq_getElem?_getD,hmx]
      rfl
    have ht : label (graftEmbed midpoint root i)=142+Q := by
      rw [htarget,hp]
      simp [alphaShift]
    refine ⟨fun v => 142+Q-label v,graceful_complement _ _ _ hgraceful,?_⟩
    simp [ht]

end GracefulBoundary.Rooted71
