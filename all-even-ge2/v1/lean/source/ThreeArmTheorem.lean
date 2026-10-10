import NearTipGraph

namespace GracefulBoundary.NearTip

theorem even_graph (r : Nat) :
    LabelOne.graph (pathGraph (2*(2*r))) ⟨2*r,by omega⟩ r=graph (2*r) := by
  change IndexedGraph.mk _ _ = IndexedGraph.mk _ _
  congr 1 <;> funext e <;> cases e <;> rfl

theorem odd_graph (r : Nat) :
    OddNearTip.graph (pathGraph (2*(2*r+1))) ⟨2*r+1,by omega⟩ r=graph (2*r+1) := by
  change IndexedGraph.mk _ _ = IndexedGraph.mk _ _
  congr 1 <;> funext e <;> cases e <;> rfl

theorem even_first_arm (r : Nat) (hr : 4≤r) :
    ∃ f : SpiderVertex 3 0 (2*r) → Nat,
      Graceful (spiderGraph 3 0 (2*r)) (3*(2*r)) f ∧ f (.arm ⟨0,by omega⟩ ⟨2*r-3,by omega⟩)=0 := by
  obtain ⟨g,hg,hm⟩ := LabelOne.midpoint_one_graceful_path (2*r) (by omega)
  obtain ⟨f,hf,hz⟩ := LabelOne.even_root_one_attachment (pathGraph (2*(2*r))) ⟨2*r,by omega⟩ (2*(2*r)) r (by omega) g hg hm
  rw [even_graph] at hf
  have size : 2*(2*r)+2*r=3*(2*r) := by omega
  rw [size] at hf
  exact ⟨fun v => f (toV (2*r) v),graceful_actual (2*r) f hf,by simpa only [toV,ite_true] using hz⟩

theorem odd_first_arm (r : Nat) (hr : 3≤r) :
    ∃ f : SpiderVertex 3 0 (2*r+1) → Nat,
      Graceful (spiderGraph 3 0 (2*r+1)) (3*(2*r+1)) f ∧ f (.arm ⟨0,by omega⟩ ⟨2*r+1-3,by omega⟩)=0 := by
  obtain ⟨g,hg,hm⟩ := LabelOne.midpoint_one_graceful_path (2*r+1) (by omega)
  let h := fun v => 2*(2*r+1)-g v
  have hh : Graceful (pathGraph (2*(2*r+1))) (2*(2*r+1)) h := graceful_complement _ _ g hg
  have root : h ⟨2*r+1,by omega⟩=2*(2*r+1)-1 := by dsimp only [h]; rw [hm]
  obtain ⟨f,hf,hz⟩ := OddNearTip.odd_root_last_attachment (pathGraph (2*(2*r+1))) ⟨2*r+1,by omega⟩ (2*(2*r+1)) r hr h hh (by omega) root
  rw [odd_graph] at hf
  have size : 2*(2*r+1)+2*r+1=3*(2*r+1) := by omega
  rw [size] at hf
  exact ⟨fun v => f (toV (2*r+1) v),graceful_actual (2*r+1) f hf,by simpa only [toV,ite_true] using hz⟩

theorem all_parity_first_arm (k : Nat) (hk : 7≤k) :
    ∃ f : SpiderVertex 3 0 k → Nat,
      Graceful (spiderGraph 3 0 k) (3*k) f ∧ f (.arm ⟨0,by omega⟩ ⟨k-3,by omega⟩)=0 := by
  by_cases he : k%2=0
  · obtain ⟨r,hr,hk'⟩ : ∃r,4≤r ∧ k=2*r := ⟨k/2,by omega,by omega⟩
    subst k; exact even_first_arm r hr
  · obtain ⟨r,hr,hk'⟩ : ∃r,3≤r ∧ k=2*r+1 := ⟨k/2,by omega,by omega⟩
    subst k; exact odd_first_arm r hr

end GracefulBoundary.NearTip
