import GapDepth
import RootedInjective

namespace GracefulBoundary.EvenRootedPrefix

open Rooted71

/-- The exact 2K-edge path interface needed by the arbitrary-residual graft. -/
def PathCert (K : Nat) (w : List Nat) : Prop :=
  w.length=2*K+1 ∧ w.Perm (List.range (2*K+1)) ∧
  (edgeDiffs w).Perm (List.range' 1 (2*K)) ∧
  crosses K w ∧ w[K]?=some K

def center (K : Nat) : Fin (2*K+1) := ⟨K,by omega⟩

def ZeroAt {W F : Type} (H : IndexedGraph W F) (root : W)
    (Q K : Nat) (i : Fin (2*K+1)) : Prop :=
  ∃ f : GraftVertices (Fin (2*K+1)) W (center K) → Nat,
    ConventionalGraceful
      (graftGraph (pathGraph (2*K)) H (center K) root) (2*K+Q) f ∧
    f (graftEmbed (center K) root i)=0

theorem reverse_cert (K : Nat) (w : List Nat) (hw : PathCert K w) :
    PathCert K w.reverse := by
  rcases hw with ⟨hlen,hv,he,ha,hm⟩
  refine ⟨by simpa using hlen,(List.reverse_perm w).trans hv,?_,
    crosses_reverse _ _ ha,?_⟩
  · rw [edgeDiffs_reverse]
    exact (List.reverse_perm (edgeDiffs w)).trans he
  · have hr : w.reverse[K]?=w[K]? := by
      have hrev := List.getElem?_reverse' (l:=w) (i:=K) (j:=K)
        (by rw [hlen]; omega)
      simpa only [hlen,show 2*K+1-1-K=K by omega] using hrev
    rw [hr]
    exact hm

theorem rooted_extreme {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q K : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hK : 1≤K) (w : List Nat) (hw : PathCert K w)
    (i : Fin (2*K+1))
    (hextreme : w[i.val]?=some 0 ∨ w[i.val]?=some (2*K)) :
    ZeroAt H root Q K i := by
  rcases hw with ⟨hlen,hv,he,ha,hm⟩
  let pf := pathLabel (2*K) w
  have hpath : Graceful (pathGraph (2*K)) (2*K) pf :=
    list_path_graceful (2*K) w hv he
  have hcut : Alpha (pathGraph (2*K)) K pf :=
    list_path_alpha (2*K) K w (by omega) ha
  have hcenter : pf (center K)=K := by
    change w.getD K 0=K
    rw [List.getD_eq_getElem?_getD,hm]
    rfl
  let label := graftLabel (center K) pf g K Q
  have hgraceful : ConventionalGraceful
      (graftGraph (pathGraph (2*K)) H (center K) root) (2*K+Q) label :=
    conventional_graft (pathGraph (2*K)) H (center K) root pf g
      K (2*K) Q hpath hg hcenter hroot hcut
  have htarget : label (graftEmbed (center K) root i)=alphaShift K Q (pf i) :=
    graftLabel_embed (center K) root pf g K Q hcenter hroot i
  rcases hextreme with hz|hmx
  · have hp : pf i=0 := by
      change w.getD i.val 0=0
      rw [List.getD_eq_getElem?_getD,hz]
      rfl
    refine ⟨label,hgraceful,?_⟩
    rw [htarget,hp]
    simp [alphaShift]
  · have hp : pf i=2*K := by
      change w.getD i.val 0=2*K
      rw [List.getD_eq_getElem?_getD,hmx]
      rfl
    have ht : label (graftEmbed (center K) root i)=2*K+Q := by
      rw [htarget,hp]
      simp [alphaShift,show ¬ 2*K≤K by omega]
    refine ⟨fun v => 2*K+Q-label v,
      conventional_complement _ _ _ hgraceful,?_⟩
    simp [ht]

theorem rooted_left {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q K d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hK : 1≤K) (w : List Nat) (hw : PathCert K w)
    (hd : d≤K)
    (hextreme : w[K-d]?=some 0 ∨ w[K-d]?=some (2*K)) :
    ZeroAt H root Q K ⟨K-d,by omega⟩ :=
  rooted_extreme H root g Q K hg hroot hK w hw ⟨K-d,by omega⟩ hextreme

theorem rooted_right {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q K d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hK : 1≤K) (w : List Nat) (hw : PathCert K w)
    (hd : d≤K)
    (hextreme : w[K-d]?=some 0 ∨ w[K-d]?=some (2*K)) :
    ZeroAt H root Q K ⟨K+d,by omega⟩ := by
  have hlen := hw.1
  have hrev : w.reverse[K+d]?=w[K-d]? := by
    have hr := List.getElem?_reverse' (l:=w) (i:=K+d) (j:=K-d)
      (by rw [hlen]; omega)
    simpa only [hlen,show 2*K+1-1-(K+d)=K-d by omega] using hr
  apply rooted_extreme H root g Q K hg hroot hK w.reverse (reverse_cert K w hw)
    ⟨K+d,by omega⟩
  rcases hextreme with hz|hm
  · left; rw [hrev]; exact hz
  · right; rw [hrev]; exact hm

theorem even_core_coverage (K d : Nat) (hK : 20≤K) (heven : K%2=0)
    (hd : 2≤d ∧ d≤GapFill.depthPrefix K) :
    AllOdd.Coverage ((K-4)/2) d := by
  by_cases old : K≤124
  · have hbound : d≤ReverseComplement.depthPrefix K := by
      simpa only [GapFill.depthPrefix,Q11.depthPrefix,old,ite_true] using hd.2
    have hid := ReverseComplement.even_prefix_identity K (by omega) heven
    have hcore : d≤ReverseComplement.corePrefix ((K-4)/2) := by
      rw [hid]
      exact hbound
    exact ReverseComplement.core_prefix_coverage ((K-4)/2) d
      (by omega) ⟨hd.1,hcore⟩
  · have hp : 61≤(K-4)/2 := by omega
    have hbound : d≤GapFill.F ((K-3)/2) := by
      simpa only [GapFill.depthPrefix,old,ite_false] using hd.2
    have heq : (K-4)/2=(K-3)/2 := by omega
    rw [heq]
    exact GapFill.all_depth_core_coverage ((K-3)/2) d (by omega)
      ⟨hd.1,hbound⟩

theorem core_path_cert (p : Nat) (c : List Nat)
    (hc : Even.GenericPathCertificate p c) :
    PathCert (2*p+4) c := by
  simpa only [PathCert,Even.GenericPathCertificate,
    show 2*(2*p+4)+1=4*p+9 by omega,
    show 2*(2*p+4)=4*p+8 by omega] using hc

theorem depth_source (K d : Nat) (hK : 20≤K) (heven : K%2=0)
    (hd : 2≤d ∧ d≤GapFill.depthPrefix K) :
    ∃ w, PathCert K w ∧
      (w[K-d]?=some 0 ∨ w[K-d]?=some (2*K)) := by
  let p := (K-4)/2
  obtain ⟨z,q,c,hpair,target⟩ := even_core_coverage K d hK heven hd
  have hcert := Even.core_pair_to_certificate p z q c hpair
  rcases hcert with ⟨_,_,_,_,hgeneric,hzero,hmax⟩
  have hKp : 2*p+4=K := by dsimp [p]; omega
  refine ⟨Even.completePath p c, ?_,?_⟩
  · rw [← hKp]
    exact core_path_cert p (Even.completePath p c) hgeneric
  · rcases target with hz|hq
    · subst d
      left
      simpa only [← hKp] using hzero
    · subst d
      right
      simpa only [← hKp,show 2*(2*p+4)=4*p+8 by omega] using hmax

/-- Unconditional arbitrary-rooted-H theorem for all even K≥20, both new arms. -/
theorem all_even_prefix {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q K d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hK : 20≤K) (heven : K%2=0)
    (hd : 2≤d ∧ d≤GapFill.depthPrefix K) :
    ZeroAt H root Q K ⟨K-d,by
      have hlt := GapFill.prefix_inside K (by omega)
      omega⟩ ∧
    ZeroAt H root Q K ⟨K+d,by
      have hlt := GapFill.prefix_inside K (by omega)
      omega⟩ := by
  obtain ⟨w,hw,hx⟩ := depth_source K d hK heven hd
  have hdk : d≤K := by
    have hlt := GapFill.prefix_inside K (by omega)
    omega
  exact ⟨rooted_left H root g Q K d hg hroot (by omega) w hw hdk hx,
    rooted_right H root g Q K d hg hroot (by omega) w hw hdk hx⟩

end GracefulBoundary.EvenRootedPrefix
