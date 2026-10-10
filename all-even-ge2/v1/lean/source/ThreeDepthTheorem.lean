import ThreeDepthPackets
namespace GracefulBoundary.EvenBoundary

theorem flexible_shell_graph (h m r : Nat) : Flexible.graph (spiderGraph h m (2*r)) .center r=FixedEven.graph (spiderGraph h m (2*r)) .center (2*r) := by
  change IndexedGraph.mk _ _ = IndexedGraph.mk _ _
  congr 1 <;> funext e <;> cases e <;> rfl

theorem three_depth_last_arm (r h m deficit : Nat) (hr : 5≤r) (hh : 1≤h) (hd : Flexible.Deficit deficit) :
    ∃(hlt : 2*r-deficit-1<2*r) (f : SpiderVertex (h+1) m (2*r) → Nat),
      Graceful (spiderGraph (h+1) m (2*r)) ((h+1)*(2*r)+m) f ∧ f (.arm ⟨h,by omega⟩ ⟨2*r-deficit-1,hlt⟩)=0 := by
  obtain ⟨g,hg,hroot⟩ := nonempty_even_residual r h m (by omega) hh
  obtain ⟨c,hc⟩ := Flexible.all_three_packets r deficit hr hd
  obtain ⟨f,hf,hzero⟩ := Flexible.zero_packet_attachment (spiderGraph h m (2*r)) .center (h*(2*r)+m) r deficit c hc g hg hroot
  rw [flexible_shell_graph] at hf
  have size : h*(2*r)+m+2*r=(h+1)*(2*r)+m := by simp only [Nat.add_mul,Nat.one_mul,Nat.add_right_comm]
  rw [size] at hf
  exact ⟨by have := hc.depthPositive; omega,fun v => f (FixedEven.Append.toV h m (2*r) v),FixedEven.Append.graceful_actual h m (2*r) ((h+1)*(2*r)+m) f hf,by simpa only [FixedEven.Append.toV,Nat.lt_irrefl,dite_false] using hzero⟩

/-- Each selected arm/deficit request has its own graceful labeling. -/
theorem all_even_three_deficits_n_ge_two (k n m deficit : Nat) (hk : 10≤k) (heven : k%2=0)
    (hn : 2≤n) (hd : Flexible.Deficit deficit) (a : Fin n) :
    ∃(hlt : k-deficit-1<k) (f : SpiderVertex n m k → Nat), Graceful (spiderGraph n m k) (n*k+m) f ∧
      f (.arm a ⟨k-deficit-1,hlt⟩)=0 := by
  obtain ⟨r,hr,rfl⟩ : ∃r,5≤r ∧ k=2*r := ⟨k/2,by omega,by omega⟩
  obtain ⟨h,rfl⟩ : ∃h,n=h+1 := ⟨n-1,by omega⟩
  obtain ⟨hlt,f,hf,hzero⟩ := three_depth_last_arm r h m deficit hr (by omega) hd
  let z : Fin (h+1) := ⟨h,by omega⟩
  exact ⟨hlt,fun v => f (NearTip.swapVertex a z v),NearTip.graceful_swap a z f hf,by simpa only [NearTip.swapVertex,NearTip.swapIndex_first] using hzero⟩

theorem all_even_three_depths_n_ge_two (k n m d : Nat) (hk : 10≤k) (heven : k%2=0)
    (hn : 2≤n) (hd : d=k-6 ∨ d=k-4 ∨ d=k-2) (a : Fin n) :
    ∃(hlt : d-1<k) (f : SpiderVertex n m k → Nat), Graceful (spiderGraph n m k) (n*k+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 := by
  rcases hd with hd|hd|hd <;> subst d
  · exact all_even_three_deficits_n_ge_two k n m 6 hk heven hn (Or.inr (Or.inr rfl)) a
  · exact all_even_three_deficits_n_ge_two k n m 4 hk heven hn (Or.inr (Or.inl rfl)) a
  · exact all_even_three_deficits_n_ge_two k n m 2 hk heven hn (Or.inl rfl) a

/-- A fixed graceful labeling cannot have zero at two distinct requested arm vertices. -/
theorem no_simultaneous_distinct_arm_zeros (k n m : Nat) (f : SpiderVertex n m k → Nat)
    (hf : Graceful (spiderGraph n m k) (n*k+m) f) (a : Fin n) (d e : Fin k) (hne : d≠e) :
    ¬(f (.arm a d)=0 ∧ f (.arm a e)=0) := by
  intro hz
  have eq := hf.vertices.injective (.arm a d) (.arm a e) (hz.1.trans hz.2.symm)
  have pair := SpiderVertex.arm.inj eq
  exact hne pair.2

theorem requested_indices_distinct (k : Nat) (hk : 10≤k) :
    k-6-1≠k-4-1 ∧ k-6-1≠k-2-1 ∧ k-4-1≠k-2-1 := by omega

end GracefulBoundary.EvenBoundary
