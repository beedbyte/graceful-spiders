import EventualDepth

namespace GracefulBoundary.AllOdd
open FixedDepth

def Coverage (p d : Nat) : Prop :=
  ∃ z q c, CorePair p z q c ∧ (d=z ∨ d=q)

def B8_2 : List Nat := [3,0,0,1,1,6,5,5,7,7,6,3,2,2,4,4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B8_2_valid : CorePair 8 2 3 B8_2 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B8_4 : List Nat := [3,3,5,0,0,1,1,2,2,5,4,6,6,7,7,4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B8_4_valid : CorePair 8 4 5 B8_4 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B8_6 : List Nat := [3,3,5,6,1,0,0,2,2,1,4,5,7,7,6,4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B8_6_valid : CorePair 8 6 7 B8_6 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B8_8 : List Nat := [3,5,2,2,4,1,1,0,0,3,7,7,6,6,5,4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B8_8_valid : CorePair 8 8 9 B8_8 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B8_10 : List Nat := [3,1,2,3,5,7,7,6,1,0,0,2,4,5,6,4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B8_10_valid : CorePair 8 10 11 B8_10 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_2 : List Nat := [3,0,0,1,1,3,2,6,8,8,7,4,6,7,5,2,4,5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B9_2_valid : CorePair 9 2 3 B9_2 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_4 : List Nat := [3,1,1,0,0,3,2,7,8,8,6,6,7,4,4,2,5,5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B9_4_valid : CorePair 9 4 5 B9_4 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_6 : List Nat := [3,1,2,4,1,0,0,2,7,7,8,8,5,3,4,6,6,5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B9_6_valid : CorePair 9 6 7 B9_6 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_8 : List Nat := [3,4,8,8,7,7,6,0,0,1,1,2,2,3,5,6,4,5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B9_8_valid : CorePair 9 8 9 B9_8 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_10 : List Nat := [3,1,2,3,5,4,6,6,1,0,0,2,4,7,7,8,8,5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B9_10_valid : CorePair 9 10 11 B9_10 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B10_2 : List Nat := [3,0,0,1,1,3,2,5,9,9,8,8,7,4,5,7,6,2,4,6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B10_2_valid : CorePair 10 2 3 B10_2 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B10_4 : List Nat := [3,7,5,0,0,1,1,2,2,4,4,3,6,5,9,9,8,8,7,6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B10_4_valid : CorePair 10 4 5 B10_4 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B10_6 : List Nat := [3,5,1,2,2,0,0,1,4,3,8,9,9,7,7,8,5,4,6,6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B10_6_valid : CorePair 10 6 7 B10_6 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B10_8 : List Nat := [3,4,7,7,5,1,1,0,0,3,2,2,6,9,9,8,8,5,4,6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B10_8_valid : CorePair 10 8 9 B10_8 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B10_10 : List Nat := [3,4,2,1,4,5,7,3,1,0,0,2,6,7,8,8,9,9,5,6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B10_10_valid : CorePair 10 10 11 B10_10 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B11_2 : List Nat := [3,0,0,1,1,3,2,6,10,10,9,9,8,5,7,8,6,4,5,2,4,7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B11_2_valid : CorePair 11 2 3 B11_2 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B11_4 : List Nat := [3,6,5,0,0,1,1,2,2,4,4,3,7,5,10,10,9,9,8,8,6,7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B11_4_valid : CorePair 11 4 5 B11_4 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B11_6 : List Nat := [3,5,1,2,2,0,0,1,4,3,7,10,10,9,9,4,5,6,6,8,8,7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B11_6_valid : CorePair 11 6 7 B11_6 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B11_8 : List Nat := [3,3,1,2,6,5,2,0,0,1,4,6,10,10,9,9,8,4,5,8,7,7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B11_8_valid : CorePair 11 8 9 B11_8 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B11_10 : List Nat := [3,3,1,2,7,6,5,5,2,0,0,1,4,4,8,10,10,9,6,8,9,7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B11_10_valid : CorePair 11 10 11 B11_10 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B12_2 : List Nat := [3,0,0,1,1,3,2,6,11,11,10,10,9,9,7,7,8,5,6,4,5,2,4,8]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B12_2_valid : CorePair 12 2 3 B12_2 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B12_4 : List Nat := [3,3,5,0,0,1,1,2,2,5,4,6,6,7,9,11,11,10,8,9,10,4,7,8]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B12_4_valid : CorePair 12 4 5 B12_4 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B12_6 : List Nat := [3,5,1,2,2,0,0,1,4,3,8,9,10,10,11,11,7,7,9,6,6,4,5,8]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B12_6_valid : CorePair 12 6 7 B12_6 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B12_8 : List Nat := [3,3,1,2,6,5,2,0,0,1,4,6,7,7,10,9,9,11,11,10,5,4,8,8]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B12_8_valid : CorePair 12 8 9 B12_8 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B12_10 : List Nat := [3,4,8,7,6,2,1,3,2,0,0,1,5,6,4,5,9,11,11,10,7,9,10,8]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B12_10_valid : CorePair 12 10 11 B12_10 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B13_2 : List Nat := [3,0,0,1,1,3,2,6,12,12,11,11,10,10,9,8,8,7,7,5,6,4,5,2,4,9]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B13_2_valid : CorePair 13 2 3 B13_2 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B13_4 : List Nat := [3,5,5,0,0,1,1,2,2,4,7,6,6,3,4,10,12,12,11,8,10,11,9,7,8,9]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B13_4_valid : CorePair 13 4 5 B13_4 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B13_6 : List Nat := [3,5,1,2,2,0,0,1,4,3,8,11,12,12,10,10,11,7,9,8,7,6,6,4,5,9]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B13_6_valid : CorePair 13 6 7 B13_6 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B13_8 : List Nat := [3,5,8,10,9,6,4,0,0,1,1,2,5,7,10,11,11,12,12,8,6,3,2,4,7,9]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B13_8_valid : CorePair 13 8 9 B13_8 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B13_10 : List Nat := [3,5,8,8,10,10,9,6,4,0,0,1,1,2,5,7,7,4,2,3,6,11,11,12,12,9]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem B13_10_valid : CorePair 13 10 11 B13_10 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

theorem small_seed (p d : Nat) (hp : 8≤p ∧ p≤13) (hd : 2≤d ∧ d≤11) :
    Coverage p d := by
  have bases : p=8 ∨ p=9 ∨ p=10 ∨ p=11 ∨ p=12 ∨ p=13 := by omega
  rcases bases with h | h | h | h | h | h
  all_goals subst p
  all_goals have depths : d=2 ∨ d=3 ∨ d=4 ∨ d=5 ∨ d=6 ∨ d=7 ∨ d=8 ∨ d=9 ∨ d=10 ∨ d=11 := by omega
  all_goals rcases depths with h | h | h | h | h | h | h | h | h | h
  all_goals subst d
  · exact ⟨2,3,B8_2,B8_2_valid,by decide⟩
  · exact ⟨2,3,B8_2,B8_2_valid,by decide⟩
  · exact ⟨4,5,B8_4,B8_4_valid,by decide⟩
  · exact ⟨4,5,B8_4,B8_4_valid,by decide⟩
  · exact ⟨6,7,B8_6,B8_6_valid,by decide⟩
  · exact ⟨6,7,B8_6,B8_6_valid,by decide⟩
  · exact ⟨8,9,B8_8,B8_8_valid,by decide⟩
  · exact ⟨8,9,B8_8,B8_8_valid,by decide⟩
  · exact ⟨10,11,B8_10,B8_10_valid,by decide⟩
  · exact ⟨10,11,B8_10,B8_10_valid,by decide⟩
  · exact ⟨2,3,B9_2,B9_2_valid,by decide⟩
  · exact ⟨2,3,B9_2,B9_2_valid,by decide⟩
  · exact ⟨4,5,B9_4,B9_4_valid,by decide⟩
  · exact ⟨4,5,B9_4,B9_4_valid,by decide⟩
  · exact ⟨6,7,B9_6,B9_6_valid,by decide⟩
  · exact ⟨6,7,B9_6,B9_6_valid,by decide⟩
  · exact ⟨8,9,B9_8,B9_8_valid,by decide⟩
  · exact ⟨8,9,B9_8,B9_8_valid,by decide⟩
  · exact ⟨10,11,B9_10,B9_10_valid,by decide⟩
  · exact ⟨10,11,B9_10,B9_10_valid,by decide⟩
  · exact ⟨2,3,B10_2,B10_2_valid,by decide⟩
  · exact ⟨2,3,B10_2,B10_2_valid,by decide⟩
  · exact ⟨4,5,B10_4,B10_4_valid,by decide⟩
  · exact ⟨4,5,B10_4,B10_4_valid,by decide⟩
  · exact ⟨6,7,B10_6,B10_6_valid,by decide⟩
  · exact ⟨6,7,B10_6,B10_6_valid,by decide⟩
  · exact ⟨8,9,B10_8,B10_8_valid,by decide⟩
  · exact ⟨8,9,B10_8,B10_8_valid,by decide⟩
  · exact ⟨10,11,B10_10,B10_10_valid,by decide⟩
  · exact ⟨10,11,B10_10,B10_10_valid,by decide⟩
  · exact ⟨2,3,B11_2,B11_2_valid,by decide⟩
  · exact ⟨2,3,B11_2,B11_2_valid,by decide⟩
  · exact ⟨4,5,B11_4,B11_4_valid,by decide⟩
  · exact ⟨4,5,B11_4,B11_4_valid,by decide⟩
  · exact ⟨6,7,B11_6,B11_6_valid,by decide⟩
  · exact ⟨6,7,B11_6,B11_6_valid,by decide⟩
  · exact ⟨8,9,B11_8,B11_8_valid,by decide⟩
  · exact ⟨8,9,B11_8,B11_8_valid,by decide⟩
  · exact ⟨10,11,B11_10,B11_10_valid,by decide⟩
  · exact ⟨10,11,B11_10,B11_10_valid,by decide⟩
  · exact ⟨2,3,B12_2,B12_2_valid,by decide⟩
  · exact ⟨2,3,B12_2,B12_2_valid,by decide⟩
  · exact ⟨4,5,B12_4,B12_4_valid,by decide⟩
  · exact ⟨4,5,B12_4,B12_4_valid,by decide⟩
  · exact ⟨6,7,B12_6,B12_6_valid,by decide⟩
  · exact ⟨6,7,B12_6,B12_6_valid,by decide⟩
  · exact ⟨8,9,B12_8,B12_8_valid,by decide⟩
  · exact ⟨8,9,B12_8,B12_8_valid,by decide⟩
  · exact ⟨10,11,B12_10,B12_10_valid,by decide⟩
  · exact ⟨10,11,B12_10,B12_10_valid,by decide⟩
  · exact ⟨2,3,B13_2,B13_2_valid,by decide⟩
  · exact ⟨2,3,B13_2,B13_2_valid,by decide⟩
  · exact ⟨4,5,B13_4,B13_4_valid,by decide⟩
  · exact ⟨4,5,B13_4,B13_4_valid,by decide⟩
  · exact ⟨6,7,B13_6,B13_6_valid,by decide⟩
  · exact ⟨6,7,B13_6,B13_6_valid,by decide⟩
  · exact ⟨8,9,B13_8,B13_8_valid,by decide⟩
  · exact ⟨8,9,B13_8,B13_8_valid,by decide⟩
  · exact ⟨10,11,B13_10,B13_10_valid,by decide⟩
  · exact ⟨10,11,B13_10,B13_10_valid,by decide⟩

end GracefulBoundary.AllOdd
