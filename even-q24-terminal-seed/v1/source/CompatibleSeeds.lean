import AllOddDepth

namespace GracefulBoundary.Compatible
open FixedDepth

def C16_12 : List Nat := [3, 3, 2, 7, 7, 5, 8, 9, 6, 4, 4, 0, 0, 1, 1, 2, 5, 6, 10, 8, 12, 13, 14, 14, 15, 15, 11, 11, 13, 10, 9, 12]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C16_12_valid : Variable.AnchoredCore 16 12 C16_12 := by
  constructor <;> decide

def C16_14 : List Nat := [3, 3, 2, 7, 10, 13, 15, 15, 14, 10, 8, 4, 4, 0, 0, 1, 1, 2, 5, 5, 6, 8, 11, 11, 9, 6, 7, 9, 12, 14, 13, 12]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C16_14_valid : Variable.AnchoredCore 16 14 C16_14 := by
  constructor <;> decide

def C16_16 : List Nat := [3, 3, 2, 7, 10, 15, 15, 14, 14, 13, 13, 9, 7, 4, 4, 0, 0, 1, 1, 2, 5, 5, 8, 10, 11, 8, 6, 6, 9, 11, 12, 12]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C16_16_valid : Variable.AnchoredCore 16 16 C16_16 := by
  constructor <;> decide

def C16_18 : List Nat := [3, 4, 2, 3, 9, 9, 7, 8, 11, 11, 14, 13, 8, 6, 5, 5, 4, 0, 0, 1, 1, 2, 6, 7, 10, 10, 13, 15, 15, 14, 12, 12]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C16_18_valid : Variable.AnchoredCore 16 18 C16_18 := by
  constructor <;> decide

def C16_20 : List Nat := [3, 3, 2, 6, 9, 9, 12, 13, 14, 14, 15, 15, 11, 11, 13, 10, 10, 7, 4, 0, 0, 1, 1, 2, 5, 4, 6, 8, 8, 5, 7, 12]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C16_20_valid : Variable.AnchoredCore 16 20 C16_20 := by
  constructor <;> decide

def C16_22 : List Nat := [3, 3, 2, 6, 6, 4, 7, 7, 8, 9, 9, 10, 14, 13, 13, 15, 15, 14, 11, 5, 4, 0, 0, 1, 1, 2, 5, 8, 12, 11, 10, 12]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C16_22_valid : Variable.AnchoredCore 16 22 C16_22 := by
  constructor <;> decide

def C16_24 : List Nat := [3, 5, 8, 10, 13, 15, 15, 14, 12, 9, 7, 4, 2, 3, 6, 8, 11, 13, 14, 11, 9, 6, 4, 0, 0, 1, 1, 2, 5, 7, 10, 12]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C16_24_valid : Variable.AnchoredCore 16 24 C16_24 := by
  constructor <;> decide

def C16_26 : List Nat := [3, 4, 2, 3, 5, 7, 8, 5, 6, 8, 9, 9, 12, 13, 14, 14, 15, 15, 11, 11, 13, 10, 10, 6, 4, 0, 0, 1, 1, 2, 7, 12]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C16_26_valid : Variable.AnchoredCore 16 26 C16_26 := by
  constructor <;> decide

def C17_12 : List Nat := [3, 3, 2, 6, 9, 11, 13, 10, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 10, 12, 15, 16, 16, 14, 14, 15, 11, 8, 6, 4, 7, 9, 12, 13]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C17_12_valid : Variable.AnchoredCore 17 12 C17_12 := by
  constructor <;> decide

def C17_14 : List Nat := [3, 3, 2, 6, 9, 11, 14, 15, 13, 10, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 10, 12, 15, 16, 16, 14, 12, 9, 7, 4, 6, 8, 11, 13]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C17_14_valid : Variable.AnchoredCore 17 14 C17_14 := by
  constructor <;> decide

def C17_16 : List Nat := [3, 6, 8, 5, 7, 8, 11, 15, 16, 16, 14, 9, 9, 7, 4, 0, 0, 1, 1, 2, 5, 3, 2, 4, 6, 11, 10, 10, 12, 12, 13, 14, 15, 13]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C17_16_valid : Variable.AnchoredCore 17 16 C17_16 := by
  constructor <;> decide

def C17_18 : List Nat := [3, 4, 2, 3, 5, 8, 11, 9, 9, 14, 14, 11, 10, 7, 8, 6, 4, 0, 0, 1, 1, 2, 7, 5, 6, 10, 12, 12, 15, 15, 16, 16, 13, 13]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C17_18_valid : Variable.AnchoredCore 17 18 C17_18 := by
  constructor <;> decide

def C17_20 : List Nat := [3, 4, 2, 3, 7, 9, 10, 15, 16, 16, 14, 12, 12, 11, 11, 10, 8, 5, 4, 0, 0, 1, 1, 2, 6, 8, 9, 6, 5, 7, 13, 14, 15, 13]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C17_20_valid : Variable.AnchoredCore 17 20 C17_20 := by
  constructor <;> decide

def C17_22 : List Nat := [3, 3, 2, 6, 8, 10, 11, 16, 16, 15, 15, 14, 14, 12, 10, 9, 6, 4, 7, 5, 4, 0, 0, 1, 1, 2, 5, 8, 9, 7, 13, 11, 12, 13]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C17_22_valid : Variable.AnchoredCore 17 22 C17_22 := by
  constructor <;> decide

def C17_24 : List Nat := [3, 4, 2, 3, 7, 9, 12, 14, 16, 16, 15, 12, 10, 7, 8, 10, 13, 15, 14, 11, 9, 5, 4, 0, 0, 1, 1, 2, 6, 6, 5, 8, 11, 13]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C17_24_valid : Variable.AnchoredCore 17 24 C17_24 := by
  constructor <;> decide

def C17_26 : List Nat := [3, 6, 9, 11, 14, 16, 16, 15, 13, 10, 8, 5, 5, 7, 10, 12, 15, 14, 12, 9, 7, 4, 2, 3, 4, 0, 0, 1, 1, 2, 6, 8, 11, 13]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C17_26_valid : Variable.AnchoredCore 17 26 C17_26 := by
  constructor <;> decide

def C18_12 : List Nat := [3, 3, 2, 6, 9, 11, 13, 10, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 10, 12, 14, 17, 17, 16, 16, 13, 15, 15, 12, 9, 7, 4, 6, 8, 11, 14]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C18_12_valid : Variable.AnchoredCore 18 12 C18_12 := by
  constructor <;> decide

def C18_14 : List Nat := [3, 3, 2, 6, 9, 10, 11, 11, 12, 12, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 10, 8, 6, 4, 7, 9, 16, 15, 14, 16, 17, 17, 15, 13, 13, 14]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C18_14_valid : Variable.AnchoredCore 18 14 C18_14 := by
  constructor <;> decide

def C18_16 : List Nat := [3, 3, 2, 7, 10, 12, 14, 15, 15, 13, 12, 9, 7, 4, 4, 0, 0, 1, 1, 2, 5, 5, 8, 10, 13, 11, 9, 6, 6, 8, 11, 16, 16, 17, 17, 14]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C18_16_valid : Variable.AnchoredCore 18 16 C18_16 := by
  constructor <;> decide

def C18_18 : List Nat := [3, 6, 9, 11, 13, 10, 8, 5, 7, 9, 12, 13, 15, 12, 10, 7, 4, 0, 0, 1, 1, 2, 5, 3, 2, 4, 6, 8, 11, 15, 14, 16, 16, 17, 17, 14]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C18_18_valid : Variable.AnchoredCore 18 18 C18_18 := by
  constructor <;> decide

def C18_20 : List Nat := [3, 6, 8, 10, 13, 12, 10, 7, 9, 11, 15, 15, 16, 16, 17, 17, 12, 9, 4, 0, 0, 1, 1, 2, 5, 3, 2, 4, 6, 5, 7, 8, 11, 13, 14, 14]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C18_20_valid : Variable.AnchoredCore 18 20 C18_20 := by
  constructor <;> decide

def C18_22 : List Nat := [3, 5, 9, 10, 8, 9, 15, 16, 16, 17, 17, 13, 14, 15, 13, 12, 11, 11, 10, 6, 4, 0, 0, 1, 1, 2, 5, 7, 6, 3, 2, 4, 7, 8, 12, 14]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C18_22_valid : Variable.AnchoredCore 18 22 C18_22 := by
  constructor <;> decide

def C18_24 : List Nat := [3, 4, 2, 3, 7, 9, 12, 12, 10, 10, 13, 15, 16, 13, 14, 16, 17, 17, 15, 11, 8, 5, 4, 0, 0, 1, 1, 2, 6, 8, 9, 6, 5, 7, 11, 14]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C18_24_valid : Variable.AnchoredCore 18 24 C18_24 := by
  constructor <;> decide

def C18_26 : List Nat := [3, 4, 2, 3, 7, 9, 12, 16, 15, 15, 17, 17, 16, 13, 14, 12, 10, 7, 8, 10, 13, 11, 9, 5, 4, 0, 0, 1, 1, 2, 6, 6, 5, 8, 11, 14]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C18_26_valid : Variable.AnchoredCore 18 26 C18_26 := by
  constructor <;> decide

def C19_12 : List Nat := [3, 3, 2, 6, 9, 11, 13, 10, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 10, 12, 14, 13, 12, 9, 7, 4, 6, 8, 11, 17, 18, 18, 16, 14, 15, 16, 17, 15]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C19_12_valid : Variable.AnchoredCore 19 12 C19_12 := by
  constructor <;> decide

def C19_14 : List Nat := [3, 5, 8, 8, 6, 3, 2, 4, 7, 10, 9, 6, 4, 0, 0, 1, 1, 2, 5, 7, 11, 9, 15, 17, 18, 18, 16, 13, 12, 11, 10, 12, 14, 16, 17, 14, 13, 15]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C19_14_valid : Variable.AnchoredCore 19 14 C19_14 := by
  constructor <;> decide

def C19_16 : List Nat := [3, 7, 11, 13, 18, 18, 17, 17, 16, 16, 14, 9, 8, 5, 4, 0, 0, 1, 1, 2, 5, 3, 2, 4, 7, 8, 6, 6, 10, 11, 9, 10, 12, 14, 15, 12, 13, 15]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C19_16_valid : Variable.AnchoredCore 19 16 C19_16 := by
  constructor <;> decide

def C19_18 : List Nat := [3, 5, 8, 10, 11, 8, 6, 3, 2, 4, 7, 9, 14, 11, 9, 6, 4, 0, 0, 1, 1, 2, 5, 7, 10, 12, 12, 14, 13, 18, 18, 17, 17, 16, 16, 13, 15, 15]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C19_18_valid : Variable.AnchoredCore 19 18 C19_18 := by
  constructor <;> decide

def C19_20 : List Nat := [3, 4, 2, 3, 5, 6, 9, 11, 14, 14, 16, 18, 18, 17, 12, 9, 7, 5, 4, 0, 0, 1, 1, 2, 8, 10, 13, 13, 11, 8, 6, 7, 10, 12, 15, 16, 17, 15]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C19_20_valid : Variable.AnchoredCore 19 20 C19_20 := by
  constructor <;> decide

def C19_22 : List Nat := [3, 3, 2, 6, 9, 11, 13, 13, 16, 14, 14, 18, 18, 17, 17, 16, 15, 10, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 10, 12, 11, 8, 6, 4, 7, 9, 12, 15]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C19_22_valid : Variable.AnchoredCore 19 22 C19_22 := by
  constructor <;> decide

def C19_24 : List Nat := [3, 3, 2, 6, 7, 4, 6, 8, 8, 9, 14, 16, 18, 18, 17, 14, 12, 10, 9, 11, 10, 5, 4, 0, 0, 1, 1, 2, 5, 7, 11, 13, 16, 17, 15, 12, 13, 15]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C19_24_valid : Variable.AnchoredCore 19 24 C19_24 := by
  constructor <;> decide

def C19_26 : List Nat := [3, 3, 2, 5, 8, 11, 13, 13, 17, 18, 18, 16, 16, 17, 14, 14, 15, 10, 7, 4, 5, 7, 9, 6, 4, 0, 0, 1, 1, 2, 6, 8, 10, 12, 11, 9, 12, 15]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C19_26_valid : Variable.AnchoredCore 19 26 C19_26 := by
  constructor <;> decide

def C20_12 : List Nat := [3, 3, 2, 6, 9, 11, 13, 10, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 10, 12, 14, 17, 18, 15, 12, 9, 7, 4, 6, 8, 11, 14, 15, 13, 17, 19, 19, 18, 16, 16]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C20_12_valid : Variable.AnchoredCore 20 12 C20_12 := by
  constructor <;> decide

def C20_14 : List Nat := [3, 3, 2, 6, 9, 10, 7, 4, 6, 8, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 11, 9, 13, 12, 14, 13, 19, 19, 18, 18, 17, 17, 16, 15, 15, 14, 10, 11, 12, 16]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C20_14_valid : Variable.AnchoredCore 20 14 C20_14 := by
  constructor <;> decide

def C20_16 : List Nat := [3, 4, 2, 3, 8, 11, 14, 12, 10, 7, 9, 9, 5, 5, 4, 0, 0, 1, 1, 2, 6, 6, 7, 8, 12, 15, 17, 19, 19, 18, 13, 10, 11, 13, 15, 14, 16, 17, 18, 16]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C20_16_valid : Variable.AnchoredCore 20 16 C20_16 := by
  constructor <;> decide

def C20_18 : List Nat := [3, 3, 2, 6, 9, 11, 14, 15, 18, 19, 19, 17, 13, 10, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 10, 12, 15, 13, 11, 8, 6, 4, 7, 9, 12, 14, 17, 18, 16, 16]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C20_18_valid : Variable.AnchoredCore 20 18 C20_18 := by
  constructor <;> decide

def C20_20 : List Nat := [3, 3, 2, 6, 9, 11, 14, 12, 10, 8, 11, 13, 15, 17, 12, 9, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 7, 4, 6, 10, 13, 14, 16, 15, 19, 19, 18, 18, 17, 16]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C20_20_valid : Variable.AnchoredCore 20 20 C20_20 := by
  constructor <;> decide

def C20_22 : List Nat := [3, 3, 2, 6, 9, 11, 14, 13, 15, 14, 19, 19, 18, 18, 17, 17, 13, 10, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 10, 12, 12, 9, 7, 4, 6, 8, 11, 15, 16, 16]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C20_22_valid : Variable.AnchoredCore 20 22 C20_22 := by
  constructor <;> decide

def C20_24 : List Nat := [3, 3, 2, 6, 10, 12, 15, 13, 11, 8, 9, 11, 14, 15, 18, 19, 19, 17, 13, 10, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 7, 4, 6, 9, 12, 14, 17, 18, 16, 16]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C20_24_valid : Variable.AnchoredCore 20 24 C20_24 := by
  constructor <;> decide

def C20_26 : List Nat := [3, 3, 2, 7, 10, 12, 15, 13, 11, 8, 6, 6, 9, 11, 14, 15, 17, 17, 16, 14, 12, 9, 7, 4, 4, 0, 0, 1, 1, 2, 5, 5, 8, 10, 13, 18, 18, 19, 19, 16]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C20_26_valid : Variable.AnchoredCore 20 26 C20_26 := by
  constructor <;> decide

def C21_12 : List Nat := [3, 7, 10, 12, 15, 13, 11, 8, 6, 5, 4, 0, 0, 1, 1, 2, 5, 3, 2, 4, 8, 10, 13, 16, 20, 20, 19, 19, 18, 15, 17, 18, 16, 14, 12, 9, 7, 6, 9, 11, 14, 17]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C21_12_valid : Variable.AnchoredCore 21 12 C21_12 := by
  constructor <;> decide

def C21_14 : List Nat := [3, 3, 2, 6, 9, 10, 7, 4, 6, 8, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 11, 9, 15, 15, 16, 20, 20, 19, 19, 18, 17, 16, 18, 14, 14, 13, 13, 12, 10, 11, 12, 17]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C21_14_valid : Variable.AnchoredCore 21 14 C21_14 := by
  constructor <;> decide

def C21_16 : List Nat := [3, 3, 2, 6, 9, 11, 14, 15, 18, 18, 13, 10, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 10, 12, 15, 13, 11, 8, 6, 4, 7, 9, 12, 14, 16, 16, 19, 19, 20, 20, 17, 17]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C21_16_valid : Variable.AnchoredCore 21 16 C21_16 := by
  constructor <;> decide

def C21_18 : List Nat := [3, 3, 2, 6, 9, 11, 10, 9, 13, 10, 7, 4, 6, 8, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 11, 14, 17, 16, 12, 12, 14, 13, 16, 19, 20, 20, 18, 18, 19, 15, 15, 17]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C21_18_valid : Variable.AnchoredCore 21 18 C21_18 := by
  constructor <;> decide

def C21_20 : List Nat := [3, 4, 2, 3, 5, 6, 9, 11, 11, 8, 6, 7, 10, 14, 12, 9, 7, 5, 4, 0, 0, 1, 1, 2, 8, 10, 13, 12, 16, 18, 18, 15, 14, 13, 17, 20, 20, 19, 19, 16, 15, 17]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C21_20_valid : Variable.AnchoredCore 21 20 C21_20 := by
  constructor <;> decide

def C21_22 : List Nat := [3, 3, 2, 6, 9, 8, 10, 9, 11, 11, 14, 18, 19, 19, 20, 20, 16, 13, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 7, 4, 6, 10, 13, 15, 15, 12, 12, 14, 17, 16, 18, 17]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C21_22_valid : Variable.AnchoredCore 21 22 C21_22 := by
  constructor <;> decide

def C21_24 : List Nat := [3, 6, 8, 5, 7, 8, 9, 9, 10, 12, 15, 20, 20, 19, 19, 18, 18, 16, 17, 15, 13, 7, 4, 0, 0, 1, 1, 2, 5, 3, 2, 4, 6, 10, 11, 13, 16, 14, 12, 11, 14, 17]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C21_24_valid : Variable.AnchoredCore 21 24 C21_24 := by
  constructor <;> decide

def C21_26 : List Nat := [3, 3, 2, 6, 9, 11, 13, 13, 14, 14, 20, 20, 19, 19, 18, 18, 17, 16, 16, 15, 15, 10, 8, 5, 4, 0, 0, 1, 1, 2, 5, 7, 10, 12, 11, 8, 6, 4, 7, 9, 12, 17]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem C21_26_valid : Variable.AnchoredCore 21 26 C21_26 := by
  constructor <;> decide

theorem compatible_seed (p a : Nat) (hp : 16≤p ∧ p≤21)
    (ha : 12≤a ∧ a≤26 ∧ a%2=0) : ∃ c, Variable.AnchoredCore p a c := by
  have sizes : p=16 ∨ p=17 ∨ p=18 ∨ p=19 ∨ p=20 ∨ p=21 := by omega
  rcases sizes with h | h | h | h | h | h
  all_goals subst p
  all_goals have anchors : a=12 ∨ a=14 ∨ a=16 ∨ a=18 ∨ a=20 ∨ a=22 ∨ a=24 ∨ a=26 := by omega
  all_goals rcases anchors with h | h | h | h | h | h | h | h
  all_goals subst a
  · exact ⟨C16_12,C16_12_valid⟩
  · exact ⟨C16_14,C16_14_valid⟩
  · exact ⟨C16_16,C16_16_valid⟩
  · exact ⟨C16_18,C16_18_valid⟩
  · exact ⟨C16_20,C16_20_valid⟩
  · exact ⟨C16_22,C16_22_valid⟩
  · exact ⟨C16_24,C16_24_valid⟩
  · exact ⟨C16_26,C16_26_valid⟩
  · exact ⟨C17_12,C17_12_valid⟩
  · exact ⟨C17_14,C17_14_valid⟩
  · exact ⟨C17_16,C17_16_valid⟩
  · exact ⟨C17_18,C17_18_valid⟩
  · exact ⟨C17_20,C17_20_valid⟩
  · exact ⟨C17_22,C17_22_valid⟩
  · exact ⟨C17_24,C17_24_valid⟩
  · exact ⟨C17_26,C17_26_valid⟩
  · exact ⟨C18_12,C18_12_valid⟩
  · exact ⟨C18_14,C18_14_valid⟩
  · exact ⟨C18_16,C18_16_valid⟩
  · exact ⟨C18_18,C18_18_valid⟩
  · exact ⟨C18_20,C18_20_valid⟩
  · exact ⟨C18_22,C18_22_valid⟩
  · exact ⟨C18_24,C18_24_valid⟩
  · exact ⟨C18_26,C18_26_valid⟩
  · exact ⟨C19_12,C19_12_valid⟩
  · exact ⟨C19_14,C19_14_valid⟩
  · exact ⟨C19_16,C19_16_valid⟩
  · exact ⟨C19_18,C19_18_valid⟩
  · exact ⟨C19_20,C19_20_valid⟩
  · exact ⟨C19_22,C19_22_valid⟩
  · exact ⟨C19_24,C19_24_valid⟩
  · exact ⟨C19_26,C19_26_valid⟩
  · exact ⟨C20_12,C20_12_valid⟩
  · exact ⟨C20_14,C20_14_valid⟩
  · exact ⟨C20_16,C20_16_valid⟩
  · exact ⟨C20_18,C20_18_valid⟩
  · exact ⟨C20_20,C20_20_valid⟩
  · exact ⟨C20_22,C20_22_valid⟩
  · exact ⟨C20_24,C20_24_valid⟩
  · exact ⟨C20_26,C20_26_valid⟩
  · exact ⟨C21_12,C21_12_valid⟩
  · exact ⟨C21_14,C21_14_valid⟩
  · exact ⟨C21_16,C21_16_valid⟩
  · exact ⟨C21_18,C21_18_valid⟩
  · exact ⟨C21_20,C21_20_valid⟩
  · exact ⟨C21_22,C21_22_valid⟩
  · exact ⟨C21_24,C21_24_valid⟩
  · exact ⟨C21_26,C21_26_valid⟩

end GracefulBoundary.Compatible
