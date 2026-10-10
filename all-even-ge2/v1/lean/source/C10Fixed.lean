import CenterBoundary
namespace GracefulBoundary.FullFixed
open EvenBoundary

def c10r9 : List Nat := [10,7,8,8,6,4,3,1,0,0,2,3,5,6,7,5,4,2,1]
theorem c10r9_even : Flexible.ExtremePacket 9 10 c10r9 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)
theorem c10r9_odd : Flexible.ExtremePacket 9 9 c10r9 := by constructor <;> first | (constructor <;> decide) | decide | (intro N; rfl)

theorem supplied_extreme_spider (r n m deficit : Nat) (hr : 3≤r) (hn : 2≤n)
    (c : List Nat) (hc : Flexible.ExtremePacket r deficit c) (a : Fin n) :
    ∃(hlt : 2*r-deficit-1<2*r) (f : SpiderVertex n m (2*r) → Nat),
      Graceful (spiderGraph n m (2*r)) (n*(2*r)+m) f ∧ f (.arm a ⟨2*r-deficit-1,hlt⟩)=0 := by
  obtain ⟨h,rfl⟩ : ∃h,n=h+1 := ⟨n-1,by omega⟩
  obtain ⟨g,hg,hroot⟩ := nonempty_even_residual r h m hr (by omega)
  obtain ⟨f,hf,htarget⟩ := Flexible.extreme_packet_attachment (spiderGraph h m (2*r)) .center (h*(2*r)+m) r deficit c hc g hg hroot
  rw [flexible_shell_graph] at hf
  have size : h*(2*r)+m+2*r=(h+1)*(2*r)+m := by simp only [Nat.add_mul,Nat.one_mul,Nat.add_right_comm]
  rw [size] at hf htarget
  let j : Fin (2*r) := ⟨2*r-deficit-1,by have := hc.depthPositive; omega⟩
  let z : Fin (h+1) := ⟨h,by omega⟩
  let f0 := fun v => f (FixedEven.Append.toV h m (2*r) v)
  have hf0 : Graceful (spiderGraph (h+1) m (2*r)) ((h+1)*(2*r)+m) f0 := FixedEven.Append.graceful_actual _ _ _ _ f hf
  have ht0 : f0 (.arm z j)=Flexible.extremeValue ((h+1)*(2*r)+m) deficit := by simpa only [f0,z,j,FixedEven.Append.toV,Nat.lt_irrefl,dite_false] using htarget
  let f1 := fun v => f0 (NearTip.swapVertex a z v)
  have hf1 := NearTip.graceful_swap a z f0 hf0
  have ht1 : f1 (.arm a j)=Flexible.extremeValue ((h+1)*(2*r)+m) deficit := by simpa only [f1,NearTip.swapVertex,NearTip.swapIndex_first] using ht0
  by_cases even : deficit%2=0
  · exact ⟨j.isLt,f1,hf1,by simpa [Flexible.extremeValue,even] using ht1⟩
  · have hm : f1 (.arm a j)=(h+1)*(2*r)+m := by simpa [Flexible.extremeValue,even] using ht1
    exact ⟨j.isLt,complementLabel ((h+1)*(2*r)+m) f1,whole_graph_graceful_complement _ _ f1 hf1,complement_maximum_zero _ f1 _ hm⟩

theorem k22_depth12 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 22 → Nat, Graceful (spiderGraph n m 22) (n*22+m) f ∧ f (.arm a ⟨11,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := supplied_extreme_spider 11 n m 10 (by decide) hn (LabelOne.step 9 c10r9) (Flexible.extreme_packet_step 9 10 c10r9 c10r9_even) a
  exact ⟨f,hf,hz⟩
theorem k22_depth13 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 22 → Nat, Graceful (spiderGraph n m 22) (n*22+m) f ∧ f (.arm a ⟨12,by decide⟩)=0 := by
  obtain ⟨hlt,f,hf,hz⟩ := supplied_extreme_spider 11 n m 9 (by decide) hn (LabelOne.step 9 c10r9) (Flexible.extreme_packet_step 9 9 c10r9 c10r9_odd) a
  exact ⟨f,hf,hz⟩

end GracefulBoundary.FullFixed
