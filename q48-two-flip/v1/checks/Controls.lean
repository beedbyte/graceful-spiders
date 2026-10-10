import Q48Family
open GracefulBoundary
open GracefulBoundary.Q48Flip
set_option maxHeartbeats 0
set_option maxRecDepth 16384
example : ∃ (hlt : 65-1<71) (f : SpiderVertex 2 0 71 → Nat), Graceful (spiderGraph 2 0 71) (2*71+0) f ∧ f (.arm ⟨0,by decide⟩ ⟨65-1,hlt⟩)=0 := selected_actual 2 2 0 65 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 66-1<71) (f : SpiderVertex 2 0 71 → Nat), Graceful (spiderGraph 2 0 71) (2*71+0) f ∧ f (.arm ⟨0,by decide⟩ ⟨66-1,hlt⟩)=0 := selected_actual 2 2 0 66 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 65-1<71) (f : SpiderVertex 2 0 71 → Nat), Graceful (spiderGraph 2 0 71) (2*71+0) f ∧ f (.arm ⟨1,by decide⟩ ⟨65-1,hlt⟩)=0 := selected_actual 2 2 0 65 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 66-1<71) (f : SpiderVertex 2 0 71 → Nat), Graceful (spiderGraph 2 0 71) (2*71+0) f ∧ f (.arm ⟨1,by decide⟩ ⟨66-1,hlt⟩)=0 := selected_actual 2 2 0 66 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 65-1<71) (f : SpiderVertex 2 1 71 → Nat), Graceful (spiderGraph 2 1 71) (2*71+1) f ∧ f (.arm ⟨0,by decide⟩ ⟨65-1,hlt⟩)=0 := selected_actual 2 2 1 65 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 66-1<71) (f : SpiderVertex 2 1 71 → Nat), Graceful (spiderGraph 2 1 71) (2*71+1) f ∧ f (.arm ⟨0,by decide⟩ ⟨66-1,hlt⟩)=0 := selected_actual 2 2 1 66 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 65-1<71) (f : SpiderVertex 2 1 71 → Nat), Graceful (spiderGraph 2 1 71) (2*71+1) f ∧ f (.arm ⟨1,by decide⟩ ⟨65-1,hlt⟩)=0 := selected_actual 2 2 1 65 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 66-1<71) (f : SpiderVertex 2 1 71 → Nat), Graceful (spiderGraph 2 1 71) (2*71+1) f ∧ f (.arm ⟨1,by decide⟩ ⟨66-1,hlt⟩)=0 := selected_actual 2 2 1 66 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 65-1<71) (f : SpiderVertex 3 2 71 → Nat), Graceful (spiderGraph 3 2 71) (3*71+2) f ∧ f (.arm ⟨0,by decide⟩ ⟨65-1,hlt⟩)=0 := selected_actual 2 3 2 65 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 66-1<71) (f : SpiderVertex 3 2 71 → Nat), Graceful (spiderGraph 3 2 71) (3*71+2) f ∧ f (.arm ⟨0,by decide⟩ ⟨66-1,hlt⟩)=0 := selected_actual 2 3 2 66 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 65-1<71) (f : SpiderVertex 3 2 71 → Nat), Graceful (spiderGraph 3 2 71) (3*71+2) f ∧ f (.arm ⟨1,by decide⟩ ⟨65-1,hlt⟩)=0 := selected_actual 2 3 2 65 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 66-1<71) (f : SpiderVertex 3 2 71 → Nat), Graceful (spiderGraph 3 2 71) (3*71+2) f ∧ f (.arm ⟨1,by decide⟩ ⟨66-1,hlt⟩)=0 := selected_actual 2 3 2 66 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 65-1<71) (f : SpiderVertex 3 2 71 → Nat), Graceful (spiderGraph 3 2 71) (3*71+2) f ∧ f (.arm ⟨2,by decide⟩ ⟨65-1,hlt⟩)=0 := selected_actual 2 3 2 65 (by decide) (by decide) ⟨2,by decide⟩ (by decide)
example : ∃ (hlt : 66-1<71) (f : SpiderVertex 3 2 71 → Nat), Graceful (spiderGraph 3 2 71) (3*71+2) f ∧ f (.arm ⟨2,by decide⟩ ⟨66-1,hlt⟩)=0 := selected_actual 2 3 2 66 (by decide) (by decide) ⟨2,by decide⟩ (by decide)
example : ∃ (hlt : 87-1<95) (f : SpiderVertex 2 0 95 → Nat), Graceful (spiderGraph 2 0 95) (2*95+0) f ∧ f (.arm ⟨0,by decide⟩ ⟨87-1,hlt⟩)=0 := selected_actual 3 2 0 87 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 88-1<95) (f : SpiderVertex 2 0 95 → Nat), Graceful (spiderGraph 2 0 95) (2*95+0) f ∧ f (.arm ⟨0,by decide⟩ ⟨88-1,hlt⟩)=0 := selected_actual 3 2 0 88 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 87-1<95) (f : SpiderVertex 2 0 95 → Nat), Graceful (spiderGraph 2 0 95) (2*95+0) f ∧ f (.arm ⟨1,by decide⟩ ⟨87-1,hlt⟩)=0 := selected_actual 3 2 0 87 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 88-1<95) (f : SpiderVertex 2 0 95 → Nat), Graceful (spiderGraph 2 0 95) (2*95+0) f ∧ f (.arm ⟨1,by decide⟩ ⟨88-1,hlt⟩)=0 := selected_actual 3 2 0 88 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 87-1<95) (f : SpiderVertex 2 1 95 → Nat), Graceful (spiderGraph 2 1 95) (2*95+1) f ∧ f (.arm ⟨0,by decide⟩ ⟨87-1,hlt⟩)=0 := selected_actual 3 2 1 87 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 88-1<95) (f : SpiderVertex 2 1 95 → Nat), Graceful (spiderGraph 2 1 95) (2*95+1) f ∧ f (.arm ⟨0,by decide⟩ ⟨88-1,hlt⟩)=0 := selected_actual 3 2 1 88 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 87-1<95) (f : SpiderVertex 2 1 95 → Nat), Graceful (spiderGraph 2 1 95) (2*95+1) f ∧ f (.arm ⟨1,by decide⟩ ⟨87-1,hlt⟩)=0 := selected_actual 3 2 1 87 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 88-1<95) (f : SpiderVertex 2 1 95 → Nat), Graceful (spiderGraph 2 1 95) (2*95+1) f ∧ f (.arm ⟨1,by decide⟩ ⟨88-1,hlt⟩)=0 := selected_actual 3 2 1 88 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 87-1<95) (f : SpiderVertex 3 2 95 → Nat), Graceful (spiderGraph 3 2 95) (3*95+2) f ∧ f (.arm ⟨0,by decide⟩ ⟨87-1,hlt⟩)=0 := selected_actual 3 3 2 87 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 88-1<95) (f : SpiderVertex 3 2 95 → Nat), Graceful (spiderGraph 3 2 95) (3*95+2) f ∧ f (.arm ⟨0,by decide⟩ ⟨88-1,hlt⟩)=0 := selected_actual 3 3 2 88 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 87-1<95) (f : SpiderVertex 3 2 95 → Nat), Graceful (spiderGraph 3 2 95) (3*95+2) f ∧ f (.arm ⟨1,by decide⟩ ⟨87-1,hlt⟩)=0 := selected_actual 3 3 2 87 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 88-1<95) (f : SpiderVertex 3 2 95 → Nat), Graceful (spiderGraph 3 2 95) (3*95+2) f ∧ f (.arm ⟨1,by decide⟩ ⟨88-1,hlt⟩)=0 := selected_actual 3 3 2 88 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 87-1<95) (f : SpiderVertex 3 2 95 → Nat), Graceful (spiderGraph 3 2 95) (3*95+2) f ∧ f (.arm ⟨2,by decide⟩ ⟨87-1,hlt⟩)=0 := selected_actual 3 3 2 87 (by decide) (by decide) ⟨2,by decide⟩ (by decide)
example : ∃ (hlt : 88-1<95) (f : SpiderVertex 3 2 95 → Nat), Graceful (spiderGraph 3 2 95) (3*95+2) f ∧ f (.arm ⟨2,by decide⟩ ⟨88-1,hlt⟩)=0 := selected_actual 3 3 2 88 (by decide) (by decide) ⟨2,by decide⟩ (by decide)
example : ∃ (hlt : 131-1<143) (f : SpiderVertex 2 0 143 → Nat), Graceful (spiderGraph 2 0 143) (2*143+0) f ∧ f (.arm ⟨0,by decide⟩ ⟨131-1,hlt⟩)=0 := selected_actual 5 2 0 131 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 132-1<143) (f : SpiderVertex 2 0 143 → Nat), Graceful (spiderGraph 2 0 143) (2*143+0) f ∧ f (.arm ⟨0,by decide⟩ ⟨132-1,hlt⟩)=0 := selected_actual 5 2 0 132 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 131-1<143) (f : SpiderVertex 2 0 143 → Nat), Graceful (spiderGraph 2 0 143) (2*143+0) f ∧ f (.arm ⟨1,by decide⟩ ⟨131-1,hlt⟩)=0 := selected_actual 5 2 0 131 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 132-1<143) (f : SpiderVertex 2 0 143 → Nat), Graceful (spiderGraph 2 0 143) (2*143+0) f ∧ f (.arm ⟨1,by decide⟩ ⟨132-1,hlt⟩)=0 := selected_actual 5 2 0 132 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 131-1<143) (f : SpiderVertex 2 1 143 → Nat), Graceful (spiderGraph 2 1 143) (2*143+1) f ∧ f (.arm ⟨0,by decide⟩ ⟨131-1,hlt⟩)=0 := selected_actual 5 2 1 131 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 132-1<143) (f : SpiderVertex 2 1 143 → Nat), Graceful (spiderGraph 2 1 143) (2*143+1) f ∧ f (.arm ⟨0,by decide⟩ ⟨132-1,hlt⟩)=0 := selected_actual 5 2 1 132 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 131-1<143) (f : SpiderVertex 2 1 143 → Nat), Graceful (spiderGraph 2 1 143) (2*143+1) f ∧ f (.arm ⟨1,by decide⟩ ⟨131-1,hlt⟩)=0 := selected_actual 5 2 1 131 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 132-1<143) (f : SpiderVertex 2 1 143 → Nat), Graceful (spiderGraph 2 1 143) (2*143+1) f ∧ f (.arm ⟨1,by decide⟩ ⟨132-1,hlt⟩)=0 := selected_actual 5 2 1 132 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 131-1<143) (f : SpiderVertex 3 2 143 → Nat), Graceful (spiderGraph 3 2 143) (3*143+2) f ∧ f (.arm ⟨0,by decide⟩ ⟨131-1,hlt⟩)=0 := selected_actual 5 3 2 131 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 132-1<143) (f : SpiderVertex 3 2 143 → Nat), Graceful (spiderGraph 3 2 143) (3*143+2) f ∧ f (.arm ⟨0,by decide⟩ ⟨132-1,hlt⟩)=0 := selected_actual 5 3 2 132 (by decide) (by decide) ⟨0,by decide⟩ (by decide)
example : ∃ (hlt : 131-1<143) (f : SpiderVertex 3 2 143 → Nat), Graceful (spiderGraph 3 2 143) (3*143+2) f ∧ f (.arm ⟨1,by decide⟩ ⟨131-1,hlt⟩)=0 := selected_actual 5 3 2 131 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 132-1<143) (f : SpiderVertex 3 2 143 → Nat), Graceful (spiderGraph 3 2 143) (3*143+2) f ∧ f (.arm ⟨1,by decide⟩ ⟨132-1,hlt⟩)=0 := selected_actual 5 3 2 132 (by decide) (by decide) ⟨1,by decide⟩ (by decide)
example : ∃ (hlt : 131-1<143) (f : SpiderVertex 3 2 143 → Nat), Graceful (spiderGraph 3 2 143) (3*143+2) f ∧ f (.arm ⟨2,by decide⟩ ⟨131-1,hlt⟩)=0 := selected_actual 5 3 2 131 (by decide) (by decide) ⟨2,by decide⟩ (by decide)
example : ∃ (hlt : 132-1<143) (f : SpiderVertex 3 2 143 → Nat), Graceful (spiderGraph 3 2 143) (3*143+2) f ∧ f (.arm ⟨2,by decide⟩ ⟨132-1,hlt⟩)=0 := selected_actual 5 3 2 132 (by decide) (by decide) ⟨2,by decide⟩ (by decide)
example (t n m d : Nat) (ht : 2≤t) (hn : 2≤n) (a : Fin n)
  (hd : d=21+22*t ∨ d=22+22*t) :
  ∃ (hlt : d-1<23+24*t) (f : SpiderVertex n m (23+24*t) → Nat),
    Graceful (spiderGraph n m (23+24*t)) (n*(23+24*t)+m) f ∧
    f (.arm a ⟨d-1,hlt⟩)=0 := selected_actual t n m d ht hn a hd
example (u n m : Nat) (hn : 2≤n) (a : Fin n) :
  (∃ f : SpiderVertex n m (71+24*u) → Nat, Graceful (spiderGraph n m (71+24*u)) (n*(71+24*u)+m) f ∧ f (.arm a ⟨66+22*u-1,by omega⟩)=0) ∧
  (∃ f : SpiderVertex n m (71+24*u) → Nat, Graceful (spiderGraph n m (71+24*u)) (n*(71+24*u)+m) f ∧ f (.arm a ⟨65+22*u-1,by omega⟩)=0) := terminal_actual u n m hn a
example : (terminalWord 0)[4]?=some 13 ∧ (terminalWord 0)[5]?=some 0 ∧
    (terminalWord 0)[6]?=some 0 ∧ (terminalWord 0)[7]?=some 1 ∧
    (terminalWord 0)[71]?=some 70 := by decide
example : ¬P20Q24.State 71 5 (terminalWord 0) := by
  intro h
  have e := h.neighbor1
  have other : (terminalWord 0)[4]?=some 13 := by decide
  change (terminalWord 0)[4]?=some 1 at e
  rw [other] at e
  contradiction
example : (spiderGraph 2 1 71).source (.leaf ⟨0,by decide⟩)=.center := rfl
example (a : Fin 2) : (spiderGraph 2 0 71).target (.arm a ⟨64,by decide⟩)=.arm a ⟨64,by decide⟩ := rfl
