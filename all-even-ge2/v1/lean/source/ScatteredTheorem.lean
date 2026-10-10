import ScatteredPackets
namespace GracefulBoundary.Scattered
open EvenBoundary.Flexible

/-- General sufficient actual-graph composition under explicit band, tip and prefix-seam proofs. -/
theorem full_if_prefix_and_deficit_band (R n m : Nat) (hr : 14≤R) (hn : 2≤n)
    (seam : 2*R-17≤GapFill.depthPrefix (2*R))
    (band : ∀deficit,9≤deficit ∧ deficit≤16 → ∃c,ExtremePacket R deficit c)
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
    have deficit : 9≤2*R-(d.val+1) ∧ 2*R-(d.val+1)≤16 := by omega
    obtain ⟨c,hc⟩ := band (2*R-(d.val+1)) deficit
    obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider R n m (2*R-(d.val+1)) (by omega) hn c hc a
    have eq : (⟨2*R-(2*R-(d.val+1))-1,hlt⟩ : Fin (2*R))=d := Fin.ext (by dsimp only; omega)
    rw [eq] at hz; exact ⟨f,hf,hz⟩

/-- Exactly the stated finite scattered-even set; each actual vertex receives its own labeling. -/
theorem scattered_full_zero_rotatability (k n m : Nat) (hk : k∈lengths) (hn : 2≤n) (v : SpiderVertex n m k) :
    ∃f : SpiderVertex n m k → Nat, Graceful (spiderGraph n m k) (n*k+m) f ∧ f v=0 := by
  obtain ⟨R,hR,rfl⟩ := listed_radius k hk
  have seam := (finite_arithmetic_gate (2*R) hk).2.2
  have tip := listed_tip_contract R hR
  exact full_if_prefix_and_deficit_band R n m (radius_lower R hR) hn seam (listed_deficit_band R · hR) ⟨tipList R,tip⟩ v

theorem scattered_full_unique_zero (k n m : Nat) (hk : k∈lengths) (hn : 2≤n) (v : SpiderVertex n m k) :
    ∃f : SpiderVertex n m k → Nat, Graceful (spiderGraph n m k) (n*k+m) f ∧ f v=0 ∧ ∀w,w≠v → 0<f w := by
  obtain ⟨f,hf,hz⟩ := scattered_full_zero_rotatability k n m hk hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have nonzero : f w≠0 := by intro h; exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

theorem exact_length_membership (k : Nat) : k∈lengths ↔
    k=28 ∨ k=36 ∨ k=38 ∨ k=40 ∨ k=42 ∨ k=44 ∨ k=54 ∨ k=56 ∨ k=58 ∨ k=72 ∨ k=74 ∨ k=90 := by
  simp [lengths]

theorem k30_not_listed : 30∉lengths := by decide

end GracefulBoundary.Scattered
