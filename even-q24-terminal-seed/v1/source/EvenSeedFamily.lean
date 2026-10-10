import EvenQ24Rooted
import EvenRootedPrefix

namespace GracefulBoundary.EvenSeedFamily
open EvenQ24
open Rooted71

/-- The literal terminal-12 criterion, with the strengthened zero-index bound. -/
def Seed (K z : Nat) (c : List Nat) : Prop := State K z c ∧ 3≤z

def word (z0 : Nat) (seed : List Nat) : List Bool → List Nat
  | [] => seed
  | b::bs => if b then Q24B4.extend (z0+2*bs.length+2*bs.count true) (word z0 seed bs)
             else P20Q24.extend (z0+2*bs.length+2*bs.count true) (word z0 seed bs)

/-- Arbitrary input seed and arbitrary B2/B4 history; no base K is fixed. -/
theorem all_states (K0 z0 : Nat) (seed : List Nat) (hseed : Seed K0 z0 seed)
    (bs : List Bool) :
    Seed (K0+24*bs.length) (z0+2*bs.length+2*bs.count true) (word z0 seed bs) := by
  induction bs with
  | nil => exact hseed
  | cons b bs ih =>
    cases b with
    | false =>
      have h := q24_preserves_B2 _ _ _ ih.1
      constructor
      · simpa [word,List.count_cons,
          show K0+24*bs.length+24=K0+24*(bs.length+1) by omega,
          show z0+2*bs.length+2*bs.count true+2=z0+2*(bs.length+1)+2*bs.count true by omega] using h
      · simp only [List.length_cons,List.count_cons]
        have hz := hseed.2
        omega
    | true =>
      have h := q24_preserves_B4 _ _ _ ih.1
      constructor
      · simpa [word,List.count_cons,
          show K0+24*bs.length+24=K0+24*(bs.length+1) by omega,
          show z0+2*bs.length+2*bs.count true+4=z0+2*(bs.length+1)+2*(bs.count true+1) by omega] using h
      · simp only [List.length_cons,List.count_cons]
        have hz := hseed.2
        omega

theorem window_arithmetic (K0 z0 t d : Nat) (hz : z0+2<K0)
    (hlo : K0-z0-1+20*t≤d) (hhi : d≤K0-z0+22*t) :
    ∃ j, j≤t ∧ (d=K0+24*t-(z0+2*t+2*j) ∨
                   d=K0+24*t-(z0+2*t+2*j+1)) := by
  let q := K0-z0+22*t-d
  have hq : q≤2*t+1 := by dsimp [q]; omega
  have hm : q%2<2 := Nat.mod_lt q (by decide)
  have hd : q=2*(q/2)+q%2 := by omega
  refine ⟨q/2,by omega,?_⟩
  have cases : q%2=0 ∨ q%2=1 := by omega
  rcases cases with h | h
  · left
    dsimp [q] at hd ⊢
    omega
  · right
    dsimp [q] at hd ⊢
    omega

/-- Universal window on the two named physical arms over any supplied
conventional graceful root-zero residual graph. The two witnesses may differ. -/
theorem rooted_window {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q K0 z0 t d : Nat) (seed : List Nat)
    (hg : ConventionalGraceful H Q g) (hroot : g root=0)
    (hseed : Seed K0 z0 seed)
    (hlo : K0-z0-1+20*t≤d) (hhi : d≤K0-z0+22*t) :
    EvenRootedPrefix.ZeroAt H root Q (K0+24*t) ⟨(K0+24*t)-d,by omega⟩ ∧
    EvenRootedPrefix.ZeroAt H root Q (K0+24*t) ⟨(K0+24*t)+d,by
      have hz := hseed.1.zeroInside.2
      omega⟩ := by
  have hz := hseed.1.zeroInside.2
  obtain ⟨j,hj,hwhich⟩ := window_arithmetic K0 z0 t d hz hlo hhi
  let c := word z0 seed (mixedHistory t j)
  have hlen := mixedHistory_length t j hj
  have hcount := mixedHistory_count t j
  have hs : State (K0+24*t) (z0+2*t+2*j) c := by
    simpa [c,hlen,hcount] using (all_states K0 z0 seed hseed (mixedHistory t j)).1
  have hc := EvenQ24Rooted.state_root_path_certificate _ _ _ hs
  have hpc : EvenRootedPrefix.PathCert (K0+24*t)
      (EvenQ24Rooted.rootWord (K0+24*t) c) := hc.1
  have ht : (EvenQ24Rooted.rootWord (K0+24*t) c)[(K0+24*t)-d]?=some 0 ∨
      (EvenQ24Rooted.rootWord (K0+24*t) c)[(K0+24*t)-d]?=some (2*(K0+24*t)) := by
    rcases hwhich with hd | hd
    · right
      have heq : (K0+24*t)-d=z0+2*t+2*j := by omega
      rw [heq]
      exact hc.2.1
    · left
      have heq : (K0+24*t)-d=z0+2*t+2*j+1 := by omega
      rw [heq]
      exact hc.2.2
  have hk := hseed.1.size
  have hdk : d≤K0+24*t := by omega
  exact ⟨EvenRootedPrefix.rooted_left H root g Q (K0+24*t) d hg hroot
      (by omega) _ hpc hdk ht,
    EvenRootedPrefix.rooted_right H root g Q (K0+24*t) d hg hroot
      (by omega) _ hpc hdk ht⟩

end GracefulBoundary.EvenSeedFamily
