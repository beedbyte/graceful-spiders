import RootZeroAttachment
import C10Fixed
namespace GracefulBoundary.FullFixed

def tip20 : List Nat := [10,9,9,8,8,7,7,6,6,5,5,4,4,3,3,2,2,1,1,0,0]
def tip22 : List Nat := [11,10,10,9,9,8,8,7,7,6,6,5,5,4,4,3,3,2,2,1,1,0,0]
theorem tip20_core : RootZeroTip.CorePacket 10 tip20 := by constructor <;> decide
theorem tip22_core : RootZeroTip.CorePacket 11 tip22 := by constructor <;> decide
theorem tip20_decoded_zero (N : Nat) : (decode N false tip20)[20]?=some 0 := by rfl
theorem tip22_decoded_zero (N : Nat) : (decode N false tip22)[22]?=some 0 := by rfl

theorem root_zero_shell_graph (h m r : Nat) : RootZeroTip.graph (spiderGraph h m (2*r)) .center r=FixedEven.graph (spiderGraph h m (2*r)) .center (2*r) := by
  change IndexedGraph.mk _ _ = IndexedGraph.mk _ _
  congr 1 <;> funext e <;> cases e <;> rfl

theorem supplied_tip_zero (r n m : Nat) (hr : 0<r) (hn : 1≤n) (c : List Nat)
    (hc : RootZeroTip.CorePacket r c) (hz : ∀N,(decode N false c)[2*r]?=some 0) (a : Fin n) :
    ∃f : SpiderVertex n m (2*r) → Nat, Graceful (spiderGraph n m (2*r)) (n*(2*r)+m) f ∧ f (.arm a ⟨2*r-1,by omega⟩)=0 := by
  obtain ⟨h,rfl⟩ : ∃h,n=h+1 := ⟨n-1,by omega⟩
  let g := residualLabel h m (2*r)
  let Q := h*(2*r)+m
  let f := RootZeroTip.label Q r c g
  have hf := RootZeroTip.packet_attachment_graceful (spiderGraph h m (2*r)) .center Q r c hc g (EvenResidual.residual_gracefulness h m r hr) rfl
  have target := hz (Q+2*r)
  rw [RootZeroTip.decoded_first Q r c hc] at target
  have index : 2*r=(2*r-1)+1 := by omega
  rw [index,List.getElem?_cons_succ] at target
  have hfzero : f (.inr ⟨2*r-1,by omega⟩)=0 := by
    dsimp only [f,RootZeroTip.label]
    rw [List.getD_eq_getElem?_getD,target]; rfl
  rw [root_zero_shell_graph] at hf
  have size : Q+2*r=(h+1)*(2*r)+m := by dsimp [Q]; simp only [Nat.add_mul,Nat.one_mul,Nat.add_right_comm]
  rw [size] at hf
  let f0 := fun v => f (FixedEven.Append.toV h m (2*r) v)
  have hf0 : Graceful (spiderGraph (h+1) m (2*r)) ((h+1)*(2*r)+m) f0 := FixedEven.Append.graceful_actual _ _ _ _ f hf
  let z : Fin (h+1) := ⟨h,by omega⟩
  have ht0 : f0 (.arm z ⟨2*r-1,by omega⟩)=0 := by simpa only [f0,z,FixedEven.Append.toV,Nat.lt_irrefl,dite_false] using hfzero
  exact ⟨fun v => f0 (NearTip.swapVertex a z v),NearTip.graceful_swap a z f0 hf0,by simpa only [NearTip.swapVertex,NearTip.swapIndex_first] using ht0⟩

theorem fixed_tip_zero (k n m : Nat) (hk : k=20 ∨ k=22) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m k → Nat, Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨k-1,by omega⟩)=0 := by
  rcases hk with hk|hk <;> subst k
  · exact supplied_tip_zero 10 n m (by decide) (by omega) tip20 tip20_core tip20_decoded_zero a
  · exact supplied_tip_zero 11 n m (by decide) (by omega) tip22 tip22_core tip22_decoded_zero a

end GracefulBoundary.FullFixed
