import EvenRootedGraft
namespace GracefulBoundary.EvenQ24Rooted
open GracefulBoundary
open GracefulBoundary.EvenQ24
open GracefulBoundary.EvenRootedGraft

/-- Exact list interface consumed by the arbitrary-root extreme graft. -/
def PathCert (K : Nat) (w : List Nat) : Prop :=
  w.length=2*K+1 ∧ w.Perm (List.range (2*K+1)) ∧
  (edgeDiffs w).Perm (List.range' 1 (2*K)) ∧
  crosses K w ∧ w[K]?=some K

def rootWord (K : Nat) (c : List Nat) : List Nat :=
  (coreLabels (2*K) c).map (fun x => 2*K-x)

theorem edgeDiffs_complement (M : Nat) (w : List Nat)
    (hb : ∀ x∈w, x≤M) : edgeDiffs (w.map (fun x=>M-x))=edgeDiffs w := by
  induction w with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      have ha := hb a (by simp)
      have hb' : ∀ x∈b::xs,x≤M := by intro x hx; exact hb x (by simp [hx])
      have hbb := hb b (by simp)
      have htail := ih hb'
      change edgeDiffs ((M-b)::List.map (fun x=>M-x) xs)=edgeDiffs (b::xs) at htail
      simp only [List.map_cons,edgeDiffs]
      rw [htail]
      simp [distance]
      omega

theorem crosses_complement (K : Nat) (w : List Nat)
    (hc : crosses (K-1) w) (hb : ∀ x∈w, x≤2*K) :
    crosses K (w.map (fun x=>2*K-x)) := by
  induction w using crosses.induct with
  | case1 => trivial
  | case2 a => trivial
  | case3 a b xs ih =>
    rcases hc with ⟨hab,hrest⟩
    have ha := hb a (by simp)
    have hbb := hb b (by simp)
    have ht : ∀ x∈b::xs,x≤2*K := by intro x hx; exact hb x (by simp [hx])
    change cross K (2*K-a) (2*K-b) ∧ crosses K ((b::xs).map (fun x=>2*K-x))
    constructor
    · rcases hab with h | h
      · right
        constructor <;> omega
      · left
        constructor <;> omega
    · exact ih hrest ht

/-- The even-state labels, complemented before grafting, form a K-cut
path certificate and retain both endpoint extremes around the midpoint. -/
theorem state_root_path_certificate (K z : Nat) (c : List Nat) (h : State K z c) :
    PathCert K (rootWord K c) ∧
    (rootWord K c)[z]?=some (2*K) ∧ (rootWord K c)[z+1]?=some 0 := by
  have hh := h.high
  have hl := h.low
  have hs := h.sums
  have hp : (coreLabels (2*K) c).Perm (List.range (2*K+1)) :=
    WholeTagged.tagged_labels K c hh hl
  have he : (edgeDiffs (coreLabels (2*K) c)).Perm (List.range' 1 (2*K)) :=
    WholeTagged.tagged_edges K c hh hl hs
  have hc : crosses (K-1) (coreLabels (2*K) c) :=
    WholeTagged.tagged_crosses K (by have := h.size; omega) c hh hl
  have hbound : ∀ x∈coreLabels (2*K) c,x≤2*K := by
    intro x hx
    have hm := hp.mem_iff.mp hx
    exact Nat.le_of_lt_succ (List.mem_range.mp hm)
  have hwordperm : (rootWord K c).Perm (List.range (2*K+1)) := by
    have hrev : (List.range (2*K+1)).reverse =
        (List.range (2*K+1)).map (fun x=>2*K-x) := by
      calc
        (List.range (2*K+1)).reverse = (List.range' 0 (2*K+1)).reverse := by
          rw [List.range_eq_range']
        _ = (List.range (2*K+1)).map (fun x=>0+(2*K+1)-1-x) := by
          rw [List.reverse_range']
        _ = (List.range (2*K+1)).map (fun x=>2*K-x) := by
          congr 1
          funext x
          omega
    have hflip : ((List.range (2*K+1)).map (fun x=>2*K-x)).Perm
        (List.range (2*K+1)) := by
      rw [← hrev]
      exact List.reverse_perm _
    exact (hp.map (fun x=>2*K-x)).trans hflip
  have hwordedges : (edgeDiffs (rootWord K c)).Perm (List.range' 1 (2*K)) := by
    rw [rootWord,edgeDiffs_complement (2*K) (coreLabels (2*K) c) hbound]
    exact he
  have hwordcross : crosses K (rootWord K c) :=
    crosses_complement K (coreLabels (2*K) c) hc hbound
  have hmid : (rootWord K c)[K]?=some K := by
    simp [rootWord,List.getElem?_map,coreLabels_lookup,h.midpoint,h.even]
    omega
  have hz : (rootWord K c)[z]?=some (2*K) := by
    simp [rootWord,List.getElem?_map,coreLabels_lookup,h.lowZero,h.zeroOdd]
  have hx : (rootWord K c)[z+1]?=some 0 := by
    have hzodd := h.zeroOdd
    simp [rootWord,List.getElem?_map,coreLabels_lookup,h.highZero,
      show (z+1)%2=0 by omega]
  refine ⟨⟨?_,hwordperm,hwordedges,hwordcross,hmid⟩,hz,hx⟩
  · simp [rootWord,coreLabels_length,h.length]

def center (K : Nat) : Fin (2*K+1) := ⟨K,by omega⟩

def ZeroAt {W F : Type} (H : IndexedGraph W F) (root : W)
    (Q K : Nat) (i : Fin (2*K+1)) : Prop :=
  ∃ f : GraftVertices (Fin (2*K+1)) W (center K) → Nat,
    ConventionalGraceful (graftGraph (pathGraph (2*K)) H (center K) root) (2*K+Q) f ∧
    f (graftEmbed (center K) root i)=0

theorem reverse_cert (K : Nat) (w : List Nat) (hw : PathCert K w) :
    PathCert K w.reverse := by
  rcases hw with ⟨hlen,hv,he,ha,hm⟩
  refine ⟨by simpa using hlen,(List.reverse_perm w).trans hv,?_ ,crosses_reverse _ _ ha,?_⟩
  · rw [edgeDiffs_reverse]
    exact (List.reverse_perm (edgeDiffs w)).trans he
  · have hr : w.reverse[K]?=w[K]? := by
      have hrev := List.getElem?_reverse' (l:=w) (i:=K) (j:=K)
        (by rw [hlen]; omega)
      simpa only [hlen,show 2*K+1-1-K=K by omega] using hrev
    rw [hr]
    exact hm

theorem rooted_extreme {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W→Nat) (Q K : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hK : 1≤K) (w : List Nat) (hw : PathCert K w)
    (i : Fin (2*K+1)) (hextreme : w[i.val]?=some 0 ∨ w[i.val]?=some (2*K)) :
    ZeroAt H root Q K i := by
  rcases hw with ⟨hlen,hv,he,ha,hm⟩
  let pf := pathLabel (2*K) w
  have hpath : Graceful (pathGraph (2*K)) (2*K) pf := list_path_graceful (2*K) w hv he
  have hcut : Alpha (pathGraph (2*K)) K pf := list_path_alpha (2*K) K w hlen ha
  have hcenter : pf (center K)=K := by
    change w.getD K 0=K
    rw [List.getD_eq_getElem?_getD,hm]
    rfl
  let label := graftLabel (center K) pf g K Q
  have hgraceful : ConventionalGraceful (graftGraph (pathGraph (2*K)) H (center K) root)
      (2*K+Q) label :=
    conventional_graft (pathGraph (2*K)) H (center K) root pf g K (2*K) Q
      hpath hg hcenter hroot hcut
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
    refine ⟨fun v => 2*K+Q-label v,conventional_complement _ _ _ hgraceful,?_⟩
    simp [ht]

/-- Generic rooted transfer of either actual extreme in the formal window.
The generic graft complements the whole graft when the selected source extreme
is 2K, so the residual root remains the specified zero-labeled vertex. -/
theorem rooted_window {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W→Nat) (Q t d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hlo : 20+20*t≤d) (hhi : d≤21+22*t) :
    ∃ j, j≤t ∧ ∃ c, State (26+24*t) (5+2*t+2*j) c ∧
      ∃ f : GraftVertices (Fin (2*(26+24*t)+1)) W (center (26+24*t)) → Nat,
        ConventionalGraceful
          (graftGraph (pathGraph (2*(26+24*t))) H (center (26+24*t)) root)
          (2*(26+24*t)+Q) f ∧
        f (graftEmbed (center (26+24*t)) root
          ⟨(26+24*t)-d,by omega⟩)=0 ∧
      ∃ fR : GraftVertices (Fin (2*(26+24*t)+1)) W (center (26+24*t)) → Nat,
        ConventionalGraceful
          (graftGraph (pathGraph (2*(26+24*t))) H (center (26+24*t)) root)
          (2*(26+24*t)+Q) fR ∧
        fR (graftEmbed (center (26+24*t)) root
          ⟨(26+24*t)+d,by omega⟩)=0 := by
  obtain ⟨j,hj,hwhich⟩ := window_arithmetic t d hlo hhi
  let c := word (mixedHistory t j)
  have hlen := mixedHistory_length t j hj
  have hcount := mixedHistory_count t j
  have hstate : State (26+24*t) (5+2*t+2*j) c := by
    dsimp [c]
    simpa [hlen,hcount] using all_states (mixedHistory t j)
  have hpc := state_root_path_certificate (26+24*t) (5+2*t+2*j) c hstate
  have hpc' : PathCert (26+24*t) (rootWord (26+24*t) c) := hpc.1
  have hcenter : (rootWord (26+24*t) c)[26+24*t]?=some (26+24*t) := hpc'.2.2.2.2
  have htarget : (rootWord (26+24*t) c)[(26+24*t)-d]?=some 0 ∨
      (rootWord (26+24*t) c)[(26+24*t)-d]?=some (2*(26+24*t)) := by
    rcases hwhich with hd|hd
    · right
      rw [hd]
      have hz := hpc.2.1
      have zeq : (26+24*t)-(21+22*t-2*j)=5+2*t+2*j := by omega
      simpa only [zeq] using hz
    · left
      rw [hd]
      have hz := hpc.2.2
      have zeq : (26+24*t)-(20+22*t-2*j)=5+2*t+2*j+1 := by omega
      simpa only [zeq] using hz
  let i : Fin (2*(26+24*t)+1) := ⟨(26+24*t)-d,by omega⟩
  have hwroot := rooted_extreme H root g Q (26+24*t) hg hroot
    (by omega) (rootWord (26+24*t) c) hpc' i htarget
  rcases hwroot with ⟨f,hf,hzero⟩
  have hleft : f (graftEmbed (center (26+24*t)) root i)=0 := by
    simpa [i] using hzero
  have hrev : (rootWord (26+24*t) c).reverse[(26+24*t)+d]?=
      (rootWord (26+24*t) c)[(26+24*t)-d]? := by
    have hlenPath := hpc'.1
    have hr := List.getElem?_reverse' (l:=rootWord (26+24*t) c)
      (i:=(26+24*t)+d) (j:=(26+24*t)-d) (by rw [hlenPath]; omega)
    simpa only [hlenPath,show 2*(26+24*t)+1-1-((26+24*t)+d)=(26+24*t)-d by omega] using hr
  have htargetR : (rootWord (26+24*t) c).reverse[(26+24*t)+d]?=some 0 ∨
      (rootWord (26+24*t) c).reverse[(26+24*t)+d]?=some (2*(26+24*t)) := by
    rw [hrev]
    exact htarget
  let iR : Fin (2*(26+24*t)+1) := ⟨(26+24*t)+d,by omega⟩
  have hright := rooted_extreme H root g Q (26+24*t) hg hroot
    (by omega) (rootWord (26+24*t) c).reverse (reverse_cert _ _ hpc') iR htargetR
  rcases hright with ⟨fR,hfR,hzeroR⟩
  refine ⟨j,hj,c,hstate,f,hf,hleft,fR,hfR,?_⟩
  simpa [iR] using hzeroR

end GracefulBoundary.EvenQ24Rooted
