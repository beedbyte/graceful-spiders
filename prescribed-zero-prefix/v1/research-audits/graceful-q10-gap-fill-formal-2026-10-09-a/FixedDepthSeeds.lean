import CoreConcat

namespace GracefulBoundary.FixedDepth

-- Exact literals from the frozen author seed contracts.
def B6_2 : List Nat := [3,0,0,1,1,3,2,4,4,5,5,2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B6_2_valid : CorePair 6 2 3 B6_2 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B6_3 : List Nat := [3,1,0,0,2,3,4,4,5,5,1,2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B6_3_valid : CorePair 6 4 3 B6_3 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B6_4 : List Nat := [3,1,1,0,0,3,2,4,4,5,5,2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B6_4_valid : CorePair 6 4 5 B6_4 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B6_5 : List Nat := [3,5,5,4,0,0,1,1,2,3,4,2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B6_5_valid : CorePair 6 6 5 B6_5 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B6_6 : List Nat := [3,3,2,1,1,0,0,4,4,5,5,2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B6_6_valid : CorePair 6 6 7 B6_6 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B6_7 : List Nat := [3,3,4,4,5,5,0,0,1,1,2,2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B6_7_valid : CorePair 6 8 7 B6_7 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B6_8 : List Nat := [3,3,2,5,5,4,4,0,0,1,1,2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B6_8_valid : CorePair 6 8 9 B6_8 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B6_10 : List Nat := [3,1,2,3,4,4,5,5,1,0,0,2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B6_10_valid : CorePair 6 10 11 B6_10 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_2 : List Nat := [3,0,0,1,1,3,2,4,4,6,7,2,5,7,8,8,6,5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B9_2_valid : CorePair 9 2 3 B9_2 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_3 : List Nat := [3,1,0,0,2,3,4,2,1,7,6,4,5,6,8,8,7,5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B9_3_valid : CorePair 9 4 3 B9_3 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_4 : List Nat := [3,1,1,0,0,3,2,4,4,6,7,2,5,7,8,8,6,5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B9_4_valid : CorePair 9 4 5 B9_4 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_5 : List Nat := [3,2,1,1,0,0,4,3,5,4,2,8,8,7,7,6,6,5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B9_5_valid : CorePair 9 6 5 B9_5 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_6 : List Nat := [3,1,2,4,1,0,0,2,5,3,6,6,4,7,7,8,8,5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B9_6_valid : CorePair 9 6 7 B9_6 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_7 : List Nat := [3,1,2,3,4,2,0,0,1,7,6,4,5,6,8,8,7,5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B9_7_valid : CorePair 9 8 7 B9_7 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_8 : List Nat := [3,1,2,3,6,6,1,0,0,2,4,4,7,7,8,8,5,5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B9_8_valid : CorePair 9 8 9 B9_8 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def B9_10 : List Nat := [3,1,2,3,5,4,6,6,1,0,0,2,4,7,7,8,8,5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem B9_10_valid : CorePair 9 10 11 B9_10 := by
  constructor
  · unfold BoundaryCore
    decide
  all_goals decide

def repeatedBlock : List Nat := B6_6
theorem repeatedBlock_boundary : BoundaryCore 6 repeatedBlock :=
  B6_6_valid.boundary

theorem seed_pair_for_depth (d : Nat) (hd : 2≤d ∧ d≤11) :
    ∃ z q c6 c9, CorePair 6 z q c6 ∧ CorePair 9 z q c9 ∧ (d=z ∨ d=q) := by
  have cases : d=2 ∨ d=3 ∨ d=4 ∨ d=5 ∨ d=6 ∨ d=7 ∨ d=8 ∨ d=9 ∨ d=10 ∨ d=11 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h
  all_goals subst d
  · exact ⟨2,3,B6_2,B9_2,B6_2_valid,B9_2_valid,by decide⟩
  · exact ⟨2,3,B6_2,B9_2,B6_2_valid,B9_2_valid,by decide⟩
  · exact ⟨4,3,B6_3,B9_3,B6_3_valid,B9_3_valid,by decide⟩
  · exact ⟨4,5,B6_4,B9_4,B6_4_valid,B9_4_valid,by decide⟩
  · exact ⟨6,5,B6_5,B9_5,B6_5_valid,B9_5_valid,by decide⟩
  · exact ⟨6,7,B6_6,B9_6,B6_6_valid,B9_6_valid,by decide⟩
  · exact ⟨8,7,B6_7,B9_7,B6_7_valid,B9_7_valid,by decide⟩
  · exact ⟨8,9,B6_8,B9_8,B6_8_valid,B9_8_valid,by decide⟩
  · exact ⟨10,11,B6_10,B9_10,B6_10_valid,B9_10_valid,by decide⟩
  · exact ⟨10,11,B6_10,B9_10,B6_10_valid,B9_10_valid,by decide⟩

end GracefulBoundary.FixedDepth
