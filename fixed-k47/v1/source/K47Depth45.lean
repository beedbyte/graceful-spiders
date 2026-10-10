import FiniteAlphaTransfer
namespace GracefulBoundary.K47Depth45

def path : List Nat := [92, 0, 94, 1, 91, 3, 90, 5, 89, 8, 83, 10, 82, 12, 81, 14, 80, 15, 79, 11, 85, 9, 86, 7, 87, 4, 93, 2, 88, 6, 84, 13, 76, 21, 69, 27, 67, 28, 62, 32, 61, 35, 55, 38, 52, 45, 48, 46, 47, 43, 53, 41, 54, 39, 57, 36, 58, 34, 59, 31, 63, 30, 65, 29, 66, 25, 68, 24, 70, 23, 72, 22, 74, 16, 78, 17, 77, 18, 75, 19, 73, 20, 71, 26, 64, 33, 60, 37, 56, 40, 51, 42, 50, 44, 49]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate : FiniteAlpha.Certificate 22 46 45 path := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem depth45_zero (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (47*n+m) f ∧ f (.arm a ⟨44,by decide⟩)=0 := by
  simpa only [Nat.mul_comm] using (FiniteAlpha.prescribed_zero 22 46 45 n m path certificate hn a).2

theorem depth45_unique_zero (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (47*n+m) f ∧ f (.arm a ⟨44,by decide⟩)=0 ∧ (∀ w, f w=0 ↔ w=.arm a ⟨44,by decide⟩) := by
  obtain ⟨f,hf,hz⟩ := depth45_zero n m hn a
  refine ⟨f,hf,hz,?_⟩
  intro w
  constructor
  · intro hw
    exact hf.vertices.injective w (.arm a ⟨44,by decide⟩) (by rw [hw,hz])
  · intro hw
    rw [hw]; exact hz

end GracefulBoundary.K47Depth45
