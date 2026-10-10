import FiniteAlphaTransfer
namespace GracefulBoundary.K47OldPackets

def path0 : List Nat := [70, 21, 74, 18, 77, 15, 80, 12, 83, 9, 86, 6, 89, 4, 88, 7, 85, 10, 82, 13, 79, 16, 76, 19, 73, 22, 72, 20, 75, 17, 78, 14, 81, 11, 84, 8, 87, 5, 91, 3, 90, 1, 92, 2, 94, 0, 93, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 69, 23, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate0 : FiniteAlpha.Certificate 22 2 3 path0 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair0 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨1,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨2,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 2 3 n m path0 certificate0 hn a

def path1 : List Nat := [70, 21, 74, 18, 77, 15, 80, 12, 83, 9, 86, 6, 89, 4, 88, 7, 85, 10, 82, 13, 79, 16, 76, 19, 73, 22, 72, 20, 75, 17, 78, 14, 81, 11, 84, 8, 87, 5, 91, 1, 94, 0, 92, 3, 90, 2, 93, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 69, 23, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate1 : FiniteAlpha.Certificate 22 6 7 path1 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair1 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨5,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨6,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 6 7 n m path1 certificate1 hn a

def path2 : List Nat := [70, 21, 74, 18, 77, 15, 80, 12, 83, 9, 86, 6, 89, 4, 88, 7, 85, 10, 82, 13, 79, 16, 76, 19, 73, 22, 72, 20, 75, 17, 78, 14, 81, 11, 84, 8, 87, 5, 91, 3, 90, 1, 94, 0, 92, 2, 93, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 69, 23, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate2 : FiniteAlpha.Certificate 22 4 5 path2 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair2 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨3,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨4,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 4 5 n m path2 certificate2 hn a

def path3 : List Nat := [70, 23, 69, 18, 79, 13, 78, 19, 74, 17, 75, 21, 73, 20, 76, 16, 80, 11, 84, 10, 85, 8, 86, 7, 87, 5, 88, 4, 92, 3, 89, 2, 93, 1, 94, 0, 90, 9, 81, 14, 77, 15, 83, 12, 82, 6, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate3 : FiniteAlpha.Certificate 22 12 13 path3 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair3 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨11,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨12,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 12 13 n m path3 certificate3 hn a

def path4 : List Nat := [70, 23, 69, 18, 79, 13, 78, 19, 74, 17, 75, 21, 73, 20, 76, 16, 80, 11, 84, 10, 85, 8, 86, 7, 87, 3, 92, 4, 89, 2, 93, 1, 94, 0, 90, 9, 81, 14, 77, 15, 83, 12, 82, 6, 88, 5, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate4 : FiniteAlpha.Certificate 22 14 15 path4 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair4 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨13,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨14,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 14 15 n m path4 certificate4 hn a

def path5 : List Nat := [70, 23, 69, 18, 79, 13, 78, 19, 74, 17, 75, 21, 73, 20, 76, 16, 80, 11, 84, 10, 85, 8, 88, 4, 92, 3, 89, 2, 93, 1, 94, 0, 90, 7, 86, 5, 87, 9, 81, 14, 77, 15, 83, 12, 82, 6, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate5 : FiniteAlpha.Certificate 22 16 17 path5 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair5 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨15,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨16,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 16 17 n m path5 certificate5 hn a

def path6 : List Nat := [70, 23, 69, 18, 79, 13, 78, 19, 74, 17, 75, 21, 73, 20, 76, 16, 80, 11, 84, 10, 87, 5, 86, 8, 88, 2, 93, 1, 94, 0, 90, 3, 92, 4, 89, 6, 85, 9, 81, 14, 77, 15, 83, 12, 82, 7, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate6 : FiniteAlpha.Certificate 22 18 19 path6 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair6 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨17,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨18,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 18 19 n m path6 certificate6 hn a

def path7 : List Nat := [70, 23, 69, 18, 79, 13, 78, 19, 74, 17, 75, 21, 73, 20, 76, 16, 80, 11, 84, 10, 85, 7, 89, 2, 93, 1, 94, 0, 90, 4, 92, 3, 87, 8, 88, 5, 86, 9, 81, 14, 77, 15, 83, 12, 82, 6, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate7 : FiniteAlpha.Certificate 22 20 21 path7 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair7 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨19,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨20,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 20 21 n m path7 certificate7 hn a

def path8 : List Nat := [70, 23, 69, 18, 79, 13, 78, 19, 74, 17, 75, 21, 73, 20, 76, 16, 80, 11, 84, 10, 89, 2, 93, 1, 94, 0, 90, 4, 92, 3, 88, 5, 87, 6, 86, 8, 85, 9, 81, 14, 77, 15, 83, 12, 82, 7, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate8 : FiniteAlpha.Certificate 22 22 23 path8 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair8 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨21,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨22,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 22 23 n m path8 certificate8 hn a

def path9 : List Nat := [70, 21, 72, 22, 74, 20, 73, 18, 76, 19, 75, 16, 79, 13, 82, 10, 85, 7, 88, 4, 91, 1, 94, 0, 92, 3, 89, 6, 86, 9, 83, 12, 80, 15, 77, 17, 78, 14, 81, 11, 84, 8, 87, 5, 90, 2, 93, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 69, 23, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate9 : FiniteAlpha.Certificate 22 24 25 path9 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair9 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨23,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨24,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 24 25 n m path9 certificate9 hn a

def path10 : List Nat := [70, 21, 73, 22, 72, 19, 76, 16, 79, 13, 82, 10, 85, 7, 88, 4, 91, 1, 94, 0, 92, 3, 89, 6, 86, 9, 83, 12, 80, 15, 77, 18, 74, 20, 75, 17, 78, 14, 81, 11, 84, 8, 87, 5, 90, 2, 93, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 69, 23, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate10 : FiniteAlpha.Certificate 22 28 29 path10 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair10 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨27,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨28,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 28 29 n m path10 certificate10 hn a

def path11 : List Nat := [70, 23, 69, 18, 73, 21, 74, 20, 78, 16, 77, 17, 76, 19, 75, 12, 79, 15, 80, 14, 84, 10, 83, 11, 82, 13, 81, 6, 90, 5, 86, 8, 85, 9, 88, 2, 92, 3, 94, 0, 93, 1, 89, 7, 87, 4, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate11 : FiniteAlpha.Certificate 22 8 9 path11 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair11 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨7,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨8,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 8 9 n m path11 certificate11 hn a

def path12 : List Nat := [70, 23, 69, 18, 73, 21, 74, 20, 78, 16, 77, 17, 76, 19, 75, 12, 79, 15, 80, 14, 84, 10, 83, 11, 82, 13, 81, 6, 89, 9, 85, 8, 86, 7, 88, 2, 94, 0, 93, 3, 87, 5, 90, 1, 92, 4, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate12 : FiniteAlpha.Certificate 22 10 11 path12 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair12 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨9,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨10,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 10 11 n m path12 certificate12 hn a

def path13 : List Nat := [70, 23, 69, 18, 73, 21, 74, 20, 78, 16, 77, 17, 76, 19, 75, 12, 87, 2, 93, 1, 94, 0, 90, 6, 84, 10, 81, 11, 83, 15, 79, 14, 80, 13, 82, 9, 85, 8, 88, 5, 86, 7, 89, 3, 92, 4, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate13 : FiniteAlpha.Certificate 22 26 27 path13 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair13 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨25,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨26,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 26 27 n m path13 certificate13 hn a

def path14 : List Nat := [70, 23, 69, 18, 76, 12, 83, 11, 85, 7, 87, 6, 88, 2, 93, 1, 94, 0, 90, 3, 92, 4, 89, 5, 84, 9, 86, 10, 80, 14, 79, 16, 78, 17, 77, 20, 75, 19, 73, 21, 74, 15, 82, 13, 81, 8, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate14 : FiniteAlpha.Certificate 22 30 31 path14 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair14 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨29,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨30,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 30 31 n m path14 certificate14 hn a

def path15 : List Nat := [70, 23, 69, 18, 81, 8, 88, 5, 86, 9, 87, 2, 92, 3, 94, 0, 93, 1, 89, 7, 83, 13, 82, 11, 78, 16, 77, 19, 76, 17, 73, 21, 74, 20, 75, 15, 79, 14, 80, 12, 84, 10, 85, 6, 90, 4, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate15 : FiniteAlpha.Certificate 22 32 33 path15 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair15 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨31,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨32,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 32 33 n m path15 certificate15 hn a

def path16 : List Nat := [70, 23, 69, 18, 81, 7, 87, 8, 89, 2, 93, 1, 94, 0, 90, 6, 84, 11, 78, 16, 77, 19, 76, 17, 73, 21, 74, 20, 75, 15, 79, 14, 80, 12, 83, 13, 82, 10, 85, 9, 86, 4, 92, 3, 88, 5, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate16 : FiniteAlpha.Certificate 22 34 35 path16 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair16 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨33,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨34,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 34 35 n m path16 certificate16 hn a

def path17 : List Nat := [70, 23, 69, 18, 81, 7, 87, 8, 90, 0, 94, 1, 93, 2, 88, 4, 89, 6, 84, 11, 78, 16, 77, 19, 76, 17, 73, 21, 74, 20, 75, 15, 79, 14, 80, 12, 83, 13, 82, 10, 85, 9, 86, 5, 92, 3, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate17 : FiniteAlpha.Certificate 22 38 37 path17 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair17 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨37,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨36,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 38 37 n m path17 certificate17 hn a

def path18 : List Nat := [70, 23, 69, 18, 81, 8, 86, 9, 89, 2, 94, 0, 93, 3, 88, 7, 83, 13, 82, 11, 78, 16, 77, 19, 76, 17, 73, 21, 74, 20, 75, 15, 79, 14, 80, 12, 84, 10, 85, 6, 90, 1, 92, 4, 87, 5, 91, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 72, 22, 71]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate18 : FiniteAlpha.Certificate 22 36 37 path18 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair18 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨35,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨36,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 36 37 n m path18 certificate18 hn a

def path19 : List Nat := [71, 22, 72, 21, 73, 20, 74, 19, 75, 18, 76, 17, 77, 16, 78, 15, 79, 14, 80, 13, 81, 12, 82, 11, 83, 10, 84, 9, 85, 8, 86, 7, 87, 6, 88, 5, 89, 4, 90, 3, 91, 2, 92, 1, 93, 0, 94, 46, 47, 45, 48, 44, 49, 43, 50, 42, 51, 41, 52, 40, 53, 39, 54, 38, 55, 37, 56, 36, 57, 35, 58, 34, 59, 33, 60, 32, 61, 31, 62, 30, 63, 29, 64, 28, 65, 27, 66, 26, 67, 25, 68, 24, 69, 23, 70]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate19 : FiniteAlpha.Certificate 22 2 1 path19 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair19 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨1,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (n*47+m) f ∧ f (.arm a ⟨0,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 22 2 1 n m path19 certificate19 hn a

theorem old_depth_zero (n m : Nat) (hn : 2≤n) (a : Fin n) (d : Fin 47) (hd : d.val≤37) :
    ∃ f : SpiderVertex n m 47 → Nat, Graceful (spiderGraph n m 47) (47*n+m) f ∧ f (.arm a d)=0 := by
  have hs : d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 ∨ d.val=4 ∨ d.val=5 ∨ d.val=6 ∨ d.val=7 ∨ d.val=8 ∨ d.val=9 ∨ d.val=10 ∨ d.val=11 ∨ d.val=12 ∨ d.val=13 ∨ d.val=14 ∨ d.val=15 ∨ d.val=16 ∨ d.val=17 ∨ d.val=18 ∨ d.val=19 ∨ d.val=20 ∨ d.val=21 ∨ d.val=22 ∨ d.val=23 ∨ d.val=24 ∨ d.val=25 ∨ d.val=26 ∨ d.val=27 ∨ d.val=28 ∨ d.val=29 ∨ d.val=30 ∨ d.val=31 ∨ d.val=32 ∨ d.val=33 ∨ d.val=34 ∨ d.val=35 ∨ d.val=36 ∨ d.val=37 := by omega
  rcases hs with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · have he : d=⟨0,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair19 n m hn a).2
  · have he : d=⟨1,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair19 n m hn a).1
  · have he : d=⟨2,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair0 n m hn a).2
  · have he : d=⟨3,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair2 n m hn a).1
  · have he : d=⟨4,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair2 n m hn a).2
  · have he : d=⟨5,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair1 n m hn a).1
  · have he : d=⟨6,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair1 n m hn a).2
  · have he : d=⟨7,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair11 n m hn a).1
  · have he : d=⟨8,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair11 n m hn a).2
  · have he : d=⟨9,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair12 n m hn a).1
  · have he : d=⟨10,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair12 n m hn a).2
  · have he : d=⟨11,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair3 n m hn a).1
  · have he : d=⟨12,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair3 n m hn a).2
  · have he : d=⟨13,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair4 n m hn a).1
  · have he : d=⟨14,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair4 n m hn a).2
  · have he : d=⟨15,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair5 n m hn a).1
  · have he : d=⟨16,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair5 n m hn a).2
  · have he : d=⟨17,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair6 n m hn a).1
  · have he : d=⟨18,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair6 n m hn a).2
  · have he : d=⟨19,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair7 n m hn a).1
  · have he : d=⟨20,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair7 n m hn a).2
  · have he : d=⟨21,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair8 n m hn a).1
  · have he : d=⟨22,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair8 n m hn a).2
  · have he : d=⟨23,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair9 n m hn a).1
  · have he : d=⟨24,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair9 n m hn a).2
  · have he : d=⟨25,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair13 n m hn a).1
  · have he : d=⟨26,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair13 n m hn a).2
  · have he : d=⟨27,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair10 n m hn a).1
  · have he : d=⟨28,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair10 n m hn a).2
  · have he : d=⟨29,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair14 n m hn a).1
  · have he : d=⟨30,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair14 n m hn a).2
  · have he : d=⟨31,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair15 n m hn a).1
  · have he : d=⟨32,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair15 n m hn a).2
  · have he : d=⟨33,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair16 n m hn a).1
  · have he : d=⟨34,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair16 n m hn a).2
  · have he : d=⟨35,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair18 n m hn a).1
  · have he : d=⟨36,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair18 n m hn a).2
  · have he : d=⟨37,by decide⟩ := Fin.ext h
    rw [he]
    simpa [Nat.mul_comm] using (pair17 n m hn a).1

end GracefulBoundary.K47OldPackets
