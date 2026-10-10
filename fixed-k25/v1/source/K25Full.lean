import K25Tip
namespace GracefulBoundary.K25Full

theorem arm_depth_zero (n m : Nat) (hn : 2≤n) (a : Fin n) (d : Fin 25) :
    ∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (25*n+m) f ∧ f (.arm a d)=0 := by
  have hs : d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 ∨ d.val=4 ∨ d.val=5 ∨ d.val=6 ∨ d.val=7 ∨ d.val=8 ∨ d.val=9 ∨ d.val=10 ∨ d.val=11 ∨ d.val=12 ∨ d.val=13 ∨ d.val=14 ∨ d.val=15 ∨ d.val=16 ∨ d.val=17 ∨ d.val=18 ∨ d.val=19 ∨ d.val=20 ∨ d.val=21 ∨ d.val=22 ∨ d.val=23 ∨ d.val=24 := by have := d.isLt; omega
  rcases hs with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · have he : d=⟨0,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair10 n m hn a).2
  · have he : d=⟨1,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair10 n m hn a).1
  · have he : d=⟨2,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair1 n m hn a).2
  · have he : d=⟨3,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair5 n m hn a).1
  · have he : d=⟨4,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair5 n m hn a).2
  · have he : d=⟨5,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair6 n m hn a).1
  · have he : d=⟨6,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair6 n m hn a).2
  · have he : d=⟨7,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair2 n m hn a).1
  · have he : d=⟨8,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair2 n m hn a).2
  · have he : d=⟨9,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair7 n m hn a).1
  · have he : d=⟨10,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair7 n m hn a).2
  · have he : d=⟨11,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair3 n m hn a).1
  · have he : d=⟨12,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair3 n m hn a).2
  · have he : d=⟨13,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair8 n m hn a).1
  · have he : d=⟨14,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair8 n m hn a).2
  · have he : d=⟨15,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair4 n m hn a).1
  · have he : d=⟨16,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair9 n m hn a).2
  · have he : d=⟨17,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair9 n m hn a).1
  · have he : d=⟨18,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair11 n m hn a).2
  · have he : d=⟨19,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair11 n m hn a).1
  · have he : d=⟨20,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair12 n m hn a).2
  · have he : d=⟨21,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair12 n m hn a).1
  · have he : d=⟨22,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Packets.pair0 n m hn a).2
  · have he : d=⟨23,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Tip.tips_prescribed_zero n m (by omega) a).2
  · have he : d=⟨24,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (K25Tip.tips_prescribed_zero n m (by omega) a).1

theorem all_vertices (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 25) :
    ∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (25*n+m) f ∧ f v=0 := by
  cases v with
  | center => exact K25Leaf.center_zero n m
  | leaf a => exact K25Leaf.leaf_zero n m a
  | arm a d => exact arm_depth_zero n m hn a d

theorem all_vertices_unique_zero (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 25) :
    ∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (25*n+m) f ∧ f v=0 ∧ (∀ w, f w=0 ↔ w=v) := by
  obtain ⟨f,hf,hv⟩ := all_vertices n m hn v
  refine ⟨f,hf,hv,?_⟩
  intro w
  constructor
  · intro hw
    exact hf.vertices.injective w v (by rw [hw,hv])
  · intro hw
    rw [hw]; exact hv

end GracefulBoundary.K25Full
