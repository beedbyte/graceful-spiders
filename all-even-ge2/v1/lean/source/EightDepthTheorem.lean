import ExtremePackets
namespace GracefulBoundary.EvenBoundary

theorem extreme_last_arm (r h m deficit : Nat) (hr : 8≤r) (hh : 1≤h) (hd : 1≤deficit ∧ deficit≤8) :
    ∃(hlt : 2*r-deficit-1<2*r) (f : SpiderVertex (h+1) m (2*r) → Nat),
      Graceful (spiderGraph (h+1) m (2*r)) ((h+1)*(2*r)+m) f ∧
      f (.arm ⟨h,by omega⟩ ⟨2*r-deficit-1,hlt⟩)=Flexible.extremeValue ((h+1)*(2*r)+m) deficit := by
  obtain ⟨g,hg,hroot⟩ := nonempty_even_residual r h m (by omega) hh
  obtain ⟨c,hc⟩ := Flexible.all_eight_extreme_packets r deficit hr hd
  obtain ⟨f,hf,htarget⟩ := Flexible.extreme_packet_attachment (spiderGraph h m (2*r)) .center (h*(2*r)+m) r deficit c hc g hg hroot
  rw [flexible_shell_graph] at hf
  have size : h*(2*r)+m+2*r=(h+1)*(2*r)+m := by simp only [Nat.add_mul,Nat.one_mul,Nat.add_right_comm]
  rw [size] at hf htarget
  exact ⟨by have := hc.depthPositive; omega,fun v => f (FixedEven.Append.toV h m (2*r) v),FixedEven.Append.graceful_actual h m (2*r) ((h+1)*(2*r)+m) f hf,by simpa only [FixedEven.Append.toV,Nat.lt_irrefl,dite_false] using htarget⟩

/-- On the actual complete spider, odd deficits place the target at the global maximum before complement. -/
theorem all_even_eight_extreme_deficits (k n m deficit : Nat) (hk : 16≤k) (heven : k%2=0)
    (hn : 2≤n) (hd : 1≤deficit ∧ deficit≤8) (a : Fin n) :
    ∃(hlt : k-deficit-1<k) (f : SpiderVertex n m k → Nat), Graceful (spiderGraph n m k) (n*k+m) f ∧
      f (.arm a ⟨k-deficit-1,hlt⟩)=Flexible.extremeValue (n*k+m) deficit := by
  obtain ⟨r,hr,rfl⟩ : ∃r,8≤r ∧ k=2*r := ⟨k/2,by omega,by omega⟩
  obtain ⟨h,rfl⟩ : ∃h,n=h+1 := ⟨n-1,by omega⟩
  obtain ⟨hlt,f,hf,htarget⟩ := extreme_last_arm r h m deficit hr (by omega) hd
  let z : Fin (h+1) := ⟨h,by omega⟩
  exact ⟨hlt,fun v => f (NearTip.swapVertex a z v),NearTip.graceful_swap a z f hf,by simpa only [NearTip.swapVertex,NearTip.swapIndex_first] using htarget⟩

theorem all_even_eight_deficits_n_ge_two (k n m deficit : Nat) (hk : 16≤k) (heven : k%2=0)
    (hn : 2≤n) (hd : 1≤deficit ∧ deficit≤8) (a : Fin n) :
    ∃(hlt : k-deficit-1<k) (f : SpiderVertex n m k → Nat), Graceful (spiderGraph n m k) (n*k+m) f ∧
      f (.arm a ⟨k-deficit-1,hlt⟩)=0 := by
  obtain ⟨hlt,f,hf,htarget⟩ := all_even_eight_extreme_deficits k n m deficit hk heven hn hd a
  by_cases even : deficit%2=0
  · exact ⟨hlt,f,hf,by simpa [Flexible.extremeValue,even] using htarget⟩
  · have maximum : f (.arm a ⟨k-deficit-1,hlt⟩)=n*k+m := by simpa [Flexible.extremeValue,even] using htarget
    exact ⟨hlt,complementLabel (n*k+m) f,whole_graph_graceful_complement _ _ f hf,complement_maximum_zero _ f _ maximum⟩

/-- Eight separate selected-depth/selected-arm requests on the actual named spider. -/
theorem all_even_eight_depths_n_ge_two (k n m d : Nat) (hk : 16≤k) (heven : k%2=0)
    (hn : 2≤n) (hd : k-8≤d ∧ d≤k-1) (a : Fin n) :
    ∃(hlt : d-1<k) (f : SpiderVertex n m k → Nat), Graceful (spiderGraph n m k) (n*k+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 := by
  have deficit : 1≤k-d ∧ k-d≤8 := by omega
  have depth : k-(k-d)=d := by omega
  simpa only [depth] using all_even_eight_deficits_n_ge_two k n m (k-d) hk heven hn deficit a

theorem eight_depth_unique_zero (k n m d : Nat) (hk : 16≤k) (heven : k%2=0)
    (hn : 2≤n) (hd : k-8≤d ∧ d≤k-1) (a : Fin n) :
    ∃(hlt : d-1<k) (f : SpiderVertex n m k → Nat), Graceful (spiderGraph n m k) (n*k+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 ∧ ∀v,v≠.arm a ⟨d-1,hlt⟩ → 0<f v := by
  obtain ⟨hlt,f,hf,hzero⟩ := all_even_eight_depths_n_ge_two k n m d hk heven hn hd a
  refine ⟨hlt,f,hf,hzero,?_⟩
  intro v hv
  have nonzero : f v≠0 := by
    intro hz
    exact hv (hf.vertices.injective v (.arm a ⟨d-1,hlt⟩) (hz.trans hzero.symm))
  omega

theorem eight_depth_index_semantics (k d : Nat) (hk : 16≤k) (hd : k-8≤d ∧ d≤k-1) :
    1≤d ∧ d-1<k ∧ d≠k := by omega

end GracefulBoundary.EvenBoundary
