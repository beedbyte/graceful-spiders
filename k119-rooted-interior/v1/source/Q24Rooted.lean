import Q24Terminal
import RootedInjective

namespace GracefulBoundary.Q24Rooted

open Rooted71

def center (p : Nat) : Fin (4*p+7) := ⟨2*p+3,by omega⟩

theorem reverse_certificate (p : Nat) (c : List Nat)
    (h : GenericPathCertificate p c) : GenericPathCertificate p c.reverse := by
  rcases h with ⟨hlen,hv,he,ha,hm⟩
  refine ⟨by simpa using hlen,(List.reverse_perm c).trans hv,?_,crosses_reverse _ _ ha,?_⟩
  · rw [edgeDiffs_reverse]
    exact (List.reverse_perm (edgeDiffs c)).trans he
  · have hr : c.reverse[2*p+3]?=c[2*p+3]? := by
      have hrev := List.getElem?_reverse' (l:=c) (i:=2*p+3) (j:=2*p+3)
        (by rw [hlen]; omega)
      simpa only [hlen,show 4*p+7-1-(2*p+3)=2*p+3 by omega] using hrev
    rw [hr]
    exact hm

theorem rooted_extreme {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q p : Nat) (hg : ConventionalGraceful H Q g) (hroot : g root=0)
    (w : List Nat) (hw : GenericPathCertificate p w) (i : Fin (4*p+7))
    (hextreme : w[i.val]?=some 0 ∨ w[i.val]?=some (4*p+6)) :
    ∃ f : GraftVertices (Fin (4*p+7)) W (center p) → Nat,
      ConventionalGraceful (graftGraph (pathGraph (4*p+6)) H (center p) root)
        (4*p+6+Q) f ∧
      f (graftEmbed (center p) root i)=0 := by
  rcases hw with ⟨hlen,hv,he,ha,hm⟩
  let pf := pathLabel (4*p+6) w
  have hpath : Graceful (pathGraph (4*p+6)) (4*p+6) pf :=
    list_path_graceful (4*p+6) w hv he
  have hcut : Alpha (pathGraph (4*p+6)) (2*p+2) pf :=
    list_path_alpha (4*p+6) (2*p+2) w (by omega) ha
  have hcenter : pf (center p)=2*p+2 := by
    change w.getD (2*p+3) 0=2*p+2
    rw [List.getD_eq_getElem?_getD,hm]
    rfl
  let label := graftLabel (center p) pf g (2*p+2) Q
  have hgraceful : ConventionalGraceful
      (graftGraph (pathGraph (4*p+6)) H (center p) root) (4*p+6+Q) label :=
    conventional_graft (pathGraph (4*p+6)) H (center p) root pf g
      (2*p+2) (4*p+6) Q hpath hg hcenter hroot hcut
  have htarget : label (graftEmbed (center p) root i)=alphaShift (2*p+2) Q (pf i) :=
    graftLabel_embed (center p) root pf g (2*p+2) Q hcenter hroot i
  rcases hextreme with hz|hmx
  · have hp : pf i=0 := by
      change w.getD i.val 0=0
      rw [List.getD_eq_getElem?_getD,hz]
      rfl
    refine ⟨label,hgraceful,?_⟩
    rw [htarget,hp]
    simp [alphaShift]
  · have hp : pf i=4*p+6 := by
      change w.getD i.val 0=4*p+6
      rw [List.getD_eq_getElem?_getD,hmx]
      rfl
    have ht : label (graftEmbed (center p) root i)=4*p+6+Q := by
      rw [htarget,hp]
      simp [alphaShift,show ¬ 4*p+6 ≤ 2*p+2 by omega]
    refine ⟨fun v => 4*p+6+Q-label v,
      conventional_complement _ _ _ hgraceful,?_⟩
    simp [ht]

theorem rooted_left {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q p d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (w : List Nat) (hw : GenericPathCertificate p w)
    (hd : d≤2*p+3)
    (hextreme : w[2*p+3-d]?=some 0 ∨ w[2*p+3-d]?=some (4*p+6)) :
    ∃ f : GraftVertices (Fin (4*p+7)) W (center p) → Nat,
      ConventionalGraceful (graftGraph (pathGraph (4*p+6)) H (center p) root)
        (4*p+6+Q) f ∧
      f (graftEmbed (center p) root (⟨2*p+3-d,by omega⟩ : Fin (4*p+7)))=0 :=
  rooted_extreme H root g Q p hg hroot w hw ⟨2*p+3-d,by omega⟩ hextreme

theorem rooted_right {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q p d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (w : List Nat) (hw : GenericPathCertificate p w)
    (hd : d≤2*p+3)
    (hextreme : w[2*p+3-d]?=some 0 ∨ w[2*p+3-d]?=some (4*p+6)) :
    ∃ f : GraftVertices (Fin (4*p+7)) W (center p) → Nat,
      ConventionalGraceful (graftGraph (pathGraph (4*p+6)) H (center p) root)
        (4*p+6+Q) f ∧
      f (graftEmbed (center p) root (⟨2*p+3+d,by omega⟩ : Fin (4*p+7)))=0 := by
  have hlen := hw.1
  have hrev : w.reverse[2*p+3+d]?=w[2*p+3-d]? := by
    have hr := List.getElem?_reverse' (l:=w) (i:=2*p+3+d) (j:=2*p+3-d)
      (by rw [hlen]; omega)
    simpa only [hlen,show 4*p+7-1-(2*p+3+d)=2*p+3-d by omega] using hr
  apply rooted_extreme H root g Q p hg hroot w.reverse (reverse_certificate p w hw)
    ⟨2*p+3+d,by omega⟩
  rcases hextreme with hz|hm
  · left; rw [hrev]; exact hz
  · right; rw [hrev]; exact hm

def source (s : Nat) : List Nat := coreLabels (94+48*s) (Q24Terminal.flipWord s)

theorem terminal_parameters (t : Nat) (ht : 1≤t) :
    2*(22+12*(t-1))+3=23+24*t ∧
    42+22*(t-1)=20+22*t ∧
    43+22*(t-1)=21+22*t := by
  omega

def ZeroAt {W F : Type} (H : IndexedGraph W F) (root : W)
    (Q p : Nat) (i : Fin (4*p+7)) : Prop :=
  ∃ f : GraftVertices (Fin (4*p+7)) W (center p) → Nat,
    ConventionalGraceful (graftGraph (pathGraph (4*p+6)) H (center p) root)
      (4*p+6+Q) f ∧
    f (graftEmbed (center p) root i)=0

theorem terminal_four_s {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q s : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) :
    ZeroAt H root Q (22+12*s)
      ⟨2*(22+12*s)+3-(42+22*s),by omega⟩ ∧
    ZeroAt H root Q (22+12*s)
      ⟨2*(22+12*s)+3-(43+22*s),by omega⟩ ∧
    ZeroAt H root Q (22+12*s)
      ⟨2*(22+12*s)+3+(42+22*s),by omega⟩ ∧
    ZeroAt H root Q (22+12*s)
      ⟨2*(22+12*s)+3+(43+22*s),by omega⟩ := by
  have hc := Q24Terminal.flip_certificate s
  rcases hc with ⟨_,_,_,_,hw,hz,hm⟩
  refine ⟨?_,?_,?_,?_⟩
  · exact rooted_left H root g Q (22+12*s) (42+22*s) hg hroot (source s) hw
      (by omega) (Or.inl hz)
  · exact rooted_left H root g Q (22+12*s) (43+22*s) hg hroot (source s) hw
      (by omega) (Or.inr hm)
  · exact rooted_right H root g Q (22+12*s) (42+22*s) hg hroot (source s) hw
      (by omega) (Or.inl hz)
  · exact rooted_right H root g Q (22+12*s) (43+22*s) hg hroot (source s) hw
      (by omega) (Or.inr hm)

/-- Exact k=23+24t rooted-residual result, with both named sides of the new path. -/
theorem terminal_four {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q t : Nat) (ht : 1≤t)
    (hg : ConventionalGraceful H Q g) (hroot : g root=0) :
    ZeroAt H root Q (22+12*(t-1))
      ⟨2*(22+12*(t-1))+3-(42+22*(t-1)),by omega⟩ ∧
    ZeroAt H root Q (22+12*(t-1))
      ⟨2*(22+12*(t-1))+3-(43+22*(t-1)),by omega⟩ ∧
    ZeroAt H root Q (22+12*(t-1))
      ⟨2*(22+12*(t-1))+3+(42+22*(t-1)),by omega⟩ ∧
    ZeroAt H root Q (22+12*(t-1))
      ⟨2*(22+12*(t-1))+3+(43+22*(t-1)),by omega⟩ :=
  terminal_four_s H root g Q (t-1) hg hroot

end GracefulBoundary.Q24Rooted
