import TerminalNormalized

namespace GracefulBoundary.TerminalSeed34
open H1Append TerminalNormalized

def seed29 : List Nat :=
  [1, 2, 2, 0, 0, 1, 4, 4, 3, 3, 6, 7, 9, 10, 12, 13, 15, 16, 18, 19, 21, 22, 24, 25, 26, 24, 23, 21, 20, 18, 17, 15, 14, 12, 11, 9, 8, 6, 5, 5, 7, 8, 10, 11, 13, 14, 16, 17, 19, 20, 22, 23, 25, 27, 29, 28, 27, 26, 28]

set_option maxRecDepth 32768 in
theorem seed_input : Input 13 seed29 := by constructor <;> decide

theorem seed_not_old_state : ¬State 13 seed29 := by
  intro h
  have hm := h.midpoint
  have hn : seed29[29]?≠some 28 := by decide
  exact hn hm

def parameter (r : Nat) := level 13 r
def armLength (r : Nat) := 2*parameter r+3
def offsets (r : Nat) := family concreteTail 13 seed29 r
def labels (r : Nat) := coreLabels (4*parameter r+6) (offsets r)

theorem arm_length_closed (r : Nat) : armLength r=30*4^r-1 := by
  have h := width_closed 13 r
  simp only [parameter,armLength]
  omega

theorem parameter_ge (r : Nat) : 13≤parameter r := level_ge 13 r

theorem path_certificate (r : Nat) (hr : 1≤r) : GenericPathCertificate (parameter r) (labels r) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  have h := family_input 13 seed29 seed_input (t+1)
  apply WholeTagged.whole_path_certificate (parameter (t+1)) (offsets (t+1))
  · have hl := h.length
    change (offsets (t+1)).length=2*(2*parameter (t+1)+3)+1
    change (offsets (t+1)).length=4*parameter (t+1)+7 at hl
    omega
  · exact h.high
  · exact h.low
  · exact h.sums
  · exact family_midpoint 13 seed29 seed_input t

theorem extreme_positions (r : Nat) :
    (labels r)[3]?=some 0 ∧ (labels r)[4]?=some (4*parameter r+6) := by
  have h5 := family_lookup 13 seed29 seed_input 3 r (by omega)
  have h6 := family_lookup 13 seed29 seed_input 4 r (by omega)
  have hz5 : (offsets r)[3]?=some 0 := h5.trans (by decide)
  have hz6 : (offsets r)[4]?=some 0 := h6.trans (by decide)
  constructor
  · unfold labels
    rw [coreLabels_lookup,hz5]
    simp
  · unfold labels
    rw [coreLabels_lookup,hz6]
    simp

/-- Both newly attached named arms; the residual is arbitrary and need not be onto. -/
theorem rooted_both {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q r d : Nat) (hr : 1≤r)
    (hg : Rooted71.ConventionalGraceful H Q g) (hroot : g root=0)
    (hd : d=armLength r-4 ∨ d=armLength r-3) :
    Q24Rooted.ZeroAt H root Q (parameter r) ⟨2*parameter r+3-d,by
      have := parameter_ge r; rcases hd with rfl|rfl <;> unfold armLength <;> omega⟩ ∧
    Q24Rooted.ZeroAt H root Q (parameter r) ⟨2*parameter r+3+d,by
      have := parameter_ge r; rcases hd with rfl|rfl <;> unfold armLength <;> omega⟩ := by
  have hp := parameter_ge r
  have he : (labels r)[2*parameter r+3-d]?=some 0 ∨
      (labels r)[2*parameter r+3-d]?=some (4*parameter r+6) := by
    rcases hd with rfl|rfl
    · right
      rw [show 2*parameter r+3-(armLength r-4)=4 by unfold armLength; omega]
      exact (extreme_positions r).2
    · left
      rw [show 2*parameter r+3-(armLength r-3)=3 by unfold armLength; omega]
      exact (extreme_positions r).1
  have hb : d≤2*parameter r+3 := by
    rcases hd with rfl|rfl <;> unfold armLength <;> omega
  exact ⟨Q24Rooted.rooted_left H root g Q (parameter r) d hg hroot (labels r)
      (path_certificate r hr) hb he,
    Q24Rooted.rooted_right H root g Q (parameter r) d hg hroot (labels r)
      (path_certificate r hr) hb he⟩

/-- Fully named target with bounds carried inside the proposition. -/
def ActualAt {W F : Type} (H : IndexedGraph W F) (root : W) (Q N mid i : Nat) : Prop :=
  ∃ (hc : mid<N+1) (hi : i<N+1)
    (f : GraftVertices (Fin (N+1)) W (⟨mid,hc⟩ : Fin (N+1)) → Nat),
    Rooted71.ConventionalGraceful (graftGraph (pathGraph N) H (⟨mid,hc⟩ : Fin (N+1)) root)
      (N+Q) f ∧ f (graftEmbed (⟨mid,hc⟩ : Fin (N+1)) root ⟨i,hi⟩)=0

theorem rooted_exact {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q r K d : Nat) (hr : 1≤r) (hK : K=30*4^r-1)
    (hg : Rooted71.ConventionalGraceful H Q g) (hroot : g root=0)
    (hd : d=K-4 ∨ d=K-3) :
    ActualAt H root Q (2*K) K (K-d) ∧ ActualAt H root Q (2*K) K (K+d) := by
  have he : K=2*parameter r+3 := by rw [hK,←arm_length_closed]; rfl
  cases he
  have h := rooted_both H root g Q r d hr hg hroot hd
  have hb : d≤2*parameter r+3 := by rcases hd with rfl|rfl <;> omega
  have ha : ActualAt H root Q (4*parameter r+6) (2*parameter r+3) (2*parameter r+3-d) ∧
      ActualAt H root Q (4*parameter r+6) (2*parameter r+3) (2*parameter r+3+d) := by
    constructor
    · obtain ⟨f,hf,hz⟩ := h.1
      exact ⟨by omega,by omega,f,hf,hz⟩
    · obtain ⟨f,hf,hz⟩ := h.2
      exact ⟨by omega,by omega,f,hf,hz⟩
  simpa only [show 2*(2*parameter r+3)=4*parameter r+6 by omega] using ha

/-- Expanded graph type with the exact closed arm length, not a finite instance. -/
theorem rooted_expanded {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q r K d : Nat) (hr : 1≤r) (hK : K=30*4^r-1)
    (hg : Rooted71.ConventionalGraceful H Q g) (hroot : g root=0)
    (hd : d=K-4 ∨ d=K-3) :
    (∃ f : GraftVertices (Fin (2*K+1)) W (⟨K,by omega⟩ : Fin (2*K+1)) → Nat,
      Rooted71.ConventionalGraceful
        (graftGraph (pathGraph (2*K)) H (⟨K,by omega⟩ : Fin (2*K+1)) root)
        (2*K+Q) f ∧
      f (graftEmbed (⟨K,by omega⟩ : Fin (2*K+1)) root ⟨K-d,by omega⟩)=0) ∧
    (∃ f : GraftVertices (Fin (2*K+1)) W (⟨K,by omega⟩ : Fin (2*K+1)) → Nat,
      Rooted71.ConventionalGraceful
        (graftGraph (pathGraph (2*K)) H (⟨K,by omega⟩ : Fin (2*K+1)) root)
        (2*K+Q) f ∧
      f (graftEmbed (⟨K,by omega⟩ : Fin (2*K+1)) root ⟨K+d,by
        rcases hd with rfl|rfl <;> omega⟩)=0) := by
  have h := rooted_exact H root g Q r K d hr hK hg hroot hd
  constructor
  · obtain ⟨hc,hi,f,hf,hz⟩ := h.1
    exact ⟨f,hf,hz⟩
  · obtain ⟨hc,hi,f,hf,hz⟩ := h.2
    exact ⟨f,hf,hz⟩

end GracefulBoundary.TerminalSeed34
