import EvenSeedFamily

namespace GracefulBoundary.EvenSeedFamily
open Rooted71

def seed30 : List Nat := [18,4,1,0,0,2,2,1,8,15,15,16,21,21,22,22,23,23,24,24,25,25,26,26,27,27,28,28,29,29,30,11,14,14,13,13,11,10,10,9,9,8,7,7,6,6,5,5,3,3,4,12,20,20,19,19,17,18,16,17,12]

def seed28 : List Nat := [16,11,8,7,7,5,4,3,1,0,0,2,3,8,14,6,2,1,5,12,13,15,11,10,6,4,9,9,28,27,27,26,26,25,25,24,24,23,23,22,22,21,21,20,20,19,19,16,17,17,15,14,10,13,18,18,12]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem seed30_valid : Seed 30 3 seed30 := by
  constructor
  · constructor <;> decide
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem seed28_valid : Seed 28 9 seed28 := by
  constructor
  · constructor <;> decide
  · decide

theorem k30_window {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q t d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hlo : 26+20*t≤d) (hhi : d≤27+22*t) :
    EvenRootedPrefix.ZeroAt H root Q (30+24*t) ⟨(30+24*t)-d,by omega⟩ ∧
    EvenRootedPrefix.ZeroAt H root Q (30+24*t) ⟨(30+24*t)+d,by omega⟩ :=
  rooted_window H root g Q 30 3 t d seed30 hg hroot seed30_valid hlo hhi

theorem k28_window {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q t d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hlo : 18+20*t≤d) (hhi : d≤19+22*t) :
    EvenRootedPrefix.ZeroAt H root Q (28+24*t) ⟨(28+24*t)-d,by omega⟩ ∧
    EvenRootedPrefix.ZeroAt H root Q (28+24*t) ⟨(28+24*t)+d,by omega⟩ :=
  rooted_window H root g Q 28 9 t d seed28 hg hroot seed28_valid hlo hhi

/-- K30's exact large-branch formula, not a table of evaluated t values. -/
theorem k30_D8_identity (t : Nat) (ht : 4≤t) :
    GapFill.depthPrefix (30+24*t)=30+24*t-19-2*((12*t-48)/11) := by
  simp only [GapFill.depthPrefix,show ¬30+24*t≤124 by omega,ite_false,GapFill.F]
  omega

theorem k30_seam_gain (t : Nat) (ht : 4≤t) :
    26+20*t≤GapFill.depthPrefix (30+24*t)+1 ∧
    GapFill.depthPrefix (30+24*t)<27+22*t := by
  simp only [GapFill.depthPrefix,show ¬30+24*t≤124 by omega,ite_false,GapFill.F]
  omega

/-- Exactly t≥4 joins the two stated intervals; earlier gaps are real inventory gaps. -/
theorem k30_exact_seam (t : Nat) :
    (26+20*t≤GapFill.depthPrefix (30+24*t)+1) ↔ 4≤t := by
  constructor
  · intro h
    by_cases h4 : 4≤t
    · exact h4
    · have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
      rcases hc with rfl | rfl | rfl | rfl <;>
        simp [GapFill.depthPrefix,Q11.depthPrefix,ReverseComplement.depthPrefix] at h
  · exact fun h => (k30_seam_gain t h).1

/-- Joined prefix over arbitrary supplied conventional graceful H on both arms. -/
theorem k30_joined_prefix {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q t d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (ht : 4≤t) (hd : 2≤d ∧ d≤27+22*t) :
    EvenRootedPrefix.ZeroAt H root Q (30+24*t) ⟨(30+24*t)-d,by omega⟩ ∧
    EvenRootedPrefix.ZeroAt H root Q (30+24*t) ⟨(30+24*t)+d,by omega⟩ := by
  by_cases old : d≤GapFill.depthPrefix (30+24*t)
  · exact EvenRootedPrefix.all_even_prefix H root g Q (30+24*t) d hg hroot
      (by omega) (by omega) ⟨hd.1,old⟩
  · have seam := (k30_seam_gain t ht).1
    exact k30_window H root g Q t d hg hroot (by omega) hd.2

end GracefulBoundary.EvenSeedFamily
