import Deficit24Arithmetic
namespace GracefulBoundary.Deficit24
open EvenBoundary.Flexible

def sourceRadii : List Nat := [9,11,12,15,17,21]
def PrefixSupply (R : Nat) : Prop :=
  ∀q,q∈sourceRadii → ∃p,TailGraft.RetainedPrefix (R-q+2) q p

theorem source_radius_bounds (q : Nat) (hq : q∈sourceRadii) : 2≤q ∧ q≤21 := by
  simp [sourceRadii] at hq; omega

def HighPrefixSupply (R : Nat) : Prop :=
  ∀q,q∈([15,17,21] : List Nat) → ∃p,TailGraft.RetainedPrefix (R-q+2) q p

/-- Four source certificates cover17..24 at any radius supplied with the three explicit prefix interfaces. -/
theorem high_deficits_from_supplied_prefixes (R c : Nat) (hr : 23≤R)
    (prefixes : HighPrefixSupply R) (hc : 17≤c ∧ c≤24) : ∃v,ExtremePacket R c v := by
  have cases : c=17 ∨ c=18 ∨ c=19 ∨ c=20 ∨ c=21 ∨ c=22 ∨ c=23 ∨ c=24 := by omega
  rcases cases with h|h|h|h|h|h|h|h <;> subst c
  · obtain ⟨p,hp⟩ := prefixes 15 (by decide); exact symbolic_graft R 15 17 (by omega) (by decide) p _ hp q15_c17
  · obtain ⟨p,hp⟩ := prefixes 15 (by decide); exact symbolic_graft R 15 18 (by omega) (by decide) p _ hp q15_c18
  · obtain ⟨p,hp⟩ := prefixes 17 (by decide); exact symbolic_graft R 17 19 (by omega) (by decide) p _ hp q17_c19
  · obtain ⟨p,hp⟩ := prefixes 17 (by decide); exact symbolic_graft R 17 20 (by omega) (by decide) p _ hp q17_c20
  · obtain ⟨p,hp⟩ := prefixes 21 (by decide); exact symbolic_graft R 21 21 (by omega) (by decide) p _ hp q21late_c21
  · obtain ⟨p,hp⟩ := prefixes 21 (by decide); exact symbolic_graft R 21 22 (by omega) (by decide) p _ hp q21late_c22
  · obtain ⟨p,hp⟩ := prefixes 21 (by decide); exact symbolic_graft R 21 23 (by omega) (by decide) p _ hp q21early_c23
  · obtain ⟨p,hp⟩ := prefixes 21 (by decide); exact symbolic_graft R 21 24 (by omega) (by decide) p _ hp q21early_c24

/-- Actual named graph transfer for every high-band deficit, under supplied prefix contracts. -/
theorem high_band_actual_spider (R n m c : Nat) (hr : 23≤R) (hn : 2≤n)
    (prefixes : HighPrefixSupply R) (hc : 17≤c ∧ c≤24) (a : Fin n) :
    ∃ (hlt : 2*R-c-1<2*R) (f : SpiderVertex n m (2*R) → Nat),
      Graceful (spiderGraph n m (2*R)) (n*(2*R)+m) f ∧ f (.arm a ⟨2*R-c-1,hlt⟩)=0 := by
  obtain ⟨u,hu⟩ := high_deficits_from_supplied_prefixes R c hr prefixes hc
  exact FullFixed.supplied_extreme_spider R n m c (by omega) hn u hu a

theorem all_deficits_from_supplied_prefixes (R c : Nat) (hr : 23≤R)
    (prefixes : PrefixSupply R) (hc : 9≤c ∧ c≤24) : ∃v,ExtremePacket R c v := by
  have cases : c=9 ∨ c=10 ∨ c=11 ∨ c=12 ∨ c=13 ∨ c=14 ∨ c=15 ∨ c=16 ∨ c=17 ∨ c=18 ∨ c=19 ∨ c=20 ∨ c=21 ∨ c=22 ∨ c=23 ∨ c=24 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst c
  · obtain ⟨p,hp⟩ := prefixes 9 (by decide); exact symbolic_graft R 9 9 (by omega) (by decide) p _ hp FullFixed.c10r9_odd
  · obtain ⟨p,hp⟩ := prefixes 9 (by decide); exact symbolic_graft R 9 10 (by omega) (by decide) p _ hp FullFixed.c10r9_even
  · obtain ⟨p,hp⟩ := prefixes 9 (by decide); exact symbolic_graft R 9 11 (by omega) (by decide) p _ hp FullFixed26.low9_c11
  · obtain ⟨p,hp⟩ := prefixes 9 (by decide); exact symbolic_graft R 9 12 (by omega) (by decide) p _ hp FullFixed26.low9_c12
  · obtain ⟨p,hp⟩ := prefixes 11 (by decide); exact symbolic_graft R 11 13 (by omega) (by decide) p _ hp Scattered.q11_high13
  · obtain ⟨p,hp⟩ := prefixes 11 (by decide); exact symbolic_graft R 11 14 (by omega) (by decide) p _ hp Scattered.q11_low14
  · obtain ⟨p,hp⟩ := prefixes 12 (by decide); exact symbolic_graft R 12 15 (by omega) (by decide) p _ hp Scattered.q12_high15
  · obtain ⟨p,hp⟩ := prefixes 12 (by decide); exact symbolic_graft R 12 16 (by omega) (by decide) p _ hp Scattered.q12_low16
  · obtain ⟨p,hp⟩ := prefixes 15 (by decide); exact symbolic_graft R 15 17 (by omega) (by decide) p _ hp q15_c17
  · obtain ⟨p,hp⟩ := prefixes 15 (by decide); exact symbolic_graft R 15 18 (by omega) (by decide) p _ hp q15_c18
  · obtain ⟨p,hp⟩ := prefixes 17 (by decide); exact symbolic_graft R 17 19 (by omega) (by decide) p _ hp q17_c19
  · obtain ⟨p,hp⟩ := prefixes 17 (by decide); exact symbolic_graft R 17 20 (by omega) (by decide) p _ hp q17_c20
  · obtain ⟨p,hp⟩ := prefixes 21 (by decide); exact symbolic_graft R 21 21 (by omega) (by decide) p _ hp q21late_c21
  · obtain ⟨p,hp⟩ := prefixes 21 (by decide); exact symbolic_graft R 21 22 (by omega) (by decide) p _ hp q21late_c22
  · obtain ⟨p,hp⟩ := prefixes 21 (by decide); exact symbolic_graft R 21 23 (by omega) (by decide) p _ hp q21early_c23
  · obtain ⟨p,hp⟩ := prefixes 21 (by decide); exact symbolic_graft R 21 24 (by omega) (by decide) p _ hp q21early_c24

/-- Symbolic actual-graph composition, with all finite interfaces stated explicitly. -/
theorem full_if_prefix_and_deficit24_band (R n m : Nat) (hr : 23≤R) (hn : 2≤n)
    (seam : 2*R-25≤GapFill.depthPrefix (2*R))
    (band : ∀c,9≤c ∧ c≤24 → ∃v,ExtremePacket R c v)
    (tip : ∃c,FullFixed.RootZeroTip.CorePacket R c ∧ ∀N,(decode N false c)[2*R]?=some 0)
    (v : SpiderVertex n m (2*R)) :
    ∃f : SpiderVertex n m (2*R) → Nat, Graceful (spiderGraph n m (2*R)) (n*(2*R)+m) f ∧ f v=0 := by
  cases v with
  | center => exact FullFixed.center_zero R n m (by omega)
  | leaf a => exact FullFixed.short_leaf_zero R n m (by omega) a
  | arm a d =>
    by_cases one : d.val=0
    · have eq : d=⟨0,by omega⟩ := Fin.ext one
      rw [eq]; exact FullFixed.depth_one_zero R n m (by omega) hn a
    by_cases last : d.val=2*R-1
    · have eq : d=⟨2*R-1,by omega⟩ := Fin.ext last
      obtain ⟨c,hc,hzero⟩ := tip
      rw [eq]; exact FullFixed.supplied_tip_zero R n m (by omega) (by omega) c hc hzero a
    by_cases hprefix : d.val+1≤GapFill.depthPrefix (2*R)
    · obtain ⟨hlt,f,hf,hz⟩ := GapFill.all_lengths_prefix_zero (2*R) n m (d.val+1) (by omega) hn a ⟨by omega,hprefix⟩
      have eq : (⟨d.val+1-1,hlt⟩ : Fin (2*R))=d := Fin.ext (by dsimp only; omega)
      rw [eq] at hz; exact ⟨f,hf,hz⟩
    by_cases near : 2*R-8≤d.val+1
    · obtain ⟨hlt,f,hf,hz⟩ := EvenBoundary.all_even_eight_depths_n_ge_two (2*R) n m (d.val+1) (by omega) (by omega) hn ⟨near,by omega⟩ a
      have eq : (⟨d.val+1-1,hlt⟩ : Fin (2*R))=d := Fin.ext (by dsimp only; omega)
      rw [eq] at hz; exact ⟨f,hf,hz⟩
    have deficit : 9≤2*R-(d.val+1) ∧ 2*R-(d.val+1)≤24 := by omega
    obtain ⟨c,hc⟩ := band (2*R-(d.val+1)) deficit
    obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider R n m (2*R-(d.val+1)) (by omega) hn c hc a
    have eq : (⟨2*R-(2*R-(d.val+1))-1,hlt⟩ : Fin (2*R))=d := Fin.ext (by dsimp only; omega)
    rw [eq] at hz; exact ⟨f,hf,hz⟩

end GracefulBoundary.Deficit24
