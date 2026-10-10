import K18Shallow

namespace GracefulBoundary.K18
open FullFixed

def tip18 : List Nat := [9,8,8,7,7,6,6,5,5,4,4,3,3,2,2,1,1,0,0]
theorem tip18_core : RootZeroTip.CorePacket 9 tip18 := by constructor <;> decide
theorem tip18_zero (N : Nat) : (decode N false tip18)[18]?=some 0 := by rfl

theorem depth8 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 18 → Nat, Graceful (spiderGraph n m 18) (n*18+m) f ∧
      f (.arm a ⟨7,by decide⟩)=0 := by
  obtain ⟨_,f,hf,hz⟩ := supplied_extreme_spider 9 n m 10 (by decide) hn c10r9 c10r9_even a
  exact ⟨f,hf,hz⟩

theorem depth9 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    ∃f : SpiderVertex n m 18 → Nat, Graceful (spiderGraph n m 18) (n*18+m) f ∧
      f (.arm a ⟨8,by decide⟩)=0 := by
  obtain ⟨_,f,hf,hz⟩ := supplied_extreme_spider 9 n m 9 (by decide) hn c10r9 c10r9_odd a
  exact ⟨f,hf,hz⟩

theorem arm_zero (n m : Nat) (hn : 2≤n) (a : Fin n) (d : Fin 18) :
    ∃f : SpiderVertex n m 18 → Nat, Graceful (spiderGraph n m 18) (n*18+m) f ∧
      f (.arm a d)=0 := by
  by_cases one : d.val=0
  · have eq : d=⟨0,by decide⟩ := Fin.ext one
    rw [eq]; exact depth_one_zero 9 n m (by decide) hn a
  by_cases tip : d.val=17
  · have eq : d=⟨17,by decide⟩ := Fin.ext tip
    rw [eq]; exact supplied_tip_zero 9 n m (by decide) (by omega) tip18 tip18_core tip18_zero a
  by_cases shallow : d.val≤6
  · have cases : d.val=1 ∨ d.val=2 ∨ d.val=3 ∨ d.val=4 ∨ d.val=5 ∨ d.val=6 := by omega
    rcases cases with h|h|h|h|h|h
    · have eq : d=⟨1,by decide⟩ := Fin.ext h
      rw [eq]; exact depth2 n m hn a
    · have eq : d=⟨2,by decide⟩ := Fin.ext h
      rw [eq]; exact depth3 n m hn a
    · have eq : d=⟨3,by decide⟩ := Fin.ext h
      rw [eq]; exact depth4 n m hn a
    · have eq : d=⟨4,by decide⟩ := Fin.ext h
      rw [eq]; exact depth5 n m hn a
    · have eq : d=⟨5,by decide⟩ := Fin.ext h
      rw [eq]; exact depth6 n m hn a
    · have eq : d=⟨6,by decide⟩ := Fin.ext h
      rw [eq]; exact depth7 n m hn a
  by_cases near : 10≤d.val+1
  · obtain ⟨hlt,f,hf,hz⟩ := EvenBoundary.all_even_eight_depths_n_ge_two 18 n m (d.val+1)
      (by decide) (by decide) hn ⟨near,by omega⟩ a
    have eq : (⟨d.val+1-1,hlt⟩ : Fin 18)=d := Fin.ext (by dsimp only; omega)
    rw [eq] at hz
    exact ⟨f,hf,hz⟩
  have middle : d.val=7 ∨ d.val=8 := by omega
  rcases middle with h|h
  · have eq : d=⟨7,by decide⟩ := Fin.ext h
    rw [eq]; exact depth8 n m hn a
  · have eq : d=⟨8,by decide⟩ := Fin.ext h
    rw [eq]; exact depth9 n m hn a

theorem full_zero_rotatability (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 18) :
    ∃f : SpiderVertex n m 18 → Nat,
      Graceful (spiderGraph n m 18) (n*18+m) f ∧ f v=0 := by
  cases v with
  | center => exact center_zero 9 n m (by decide)
  | arm a d => exact arm_zero n m hn a d
  | leaf a => exact short_leaf_zero 9 n m (by decide) a

theorem full_unique_zero (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 18) :
    ∃f : SpiderVertex n m 18 → Nat,
      Graceful (spiderGraph n m 18) (n*18+m) f ∧ f v=0 ∧ ∀w,w≠v → 0<f w := by
  obtain ⟨f,hf,hz⟩ := full_zero_rotatability n m hn v
  refine ⟨f,hf,hz,?_⟩
  intro w hw
  have nonzero : f w≠0 := by intro h; exact hw (hf.vertices.injective w v (h.trans hz.symm))
  omega

end GracefulBoundary.K18
