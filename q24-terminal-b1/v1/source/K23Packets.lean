import FiniteAlphaTransfer
namespace GracefulBoundary.K23Packets

def path0 : List Nat := [34, 9, 38, 6, 41, 4, 40, 7, 37, 10, 36, 8, 39, 5, 43, 3, 42, 1, 44, 2, 46, 0, 45, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 13, 32, 12, 33, 11, 35]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate0 : FiniteAlpha.Certificate 10 2 3 path0 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair0 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨1,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨2,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 2 3 n m path0 certificate0 hn a

def path1 : List Nat := [34, 9, 36, 10, 38, 8, 37, 6, 41, 3, 44, 0, 46, 1, 43, 4, 40, 7, 39, 5, 42, 2, 45, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 13, 32, 12, 33, 11, 35]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate1 : FiniteAlpha.Certificate 10 12 11 path1 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair1 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨11,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨10,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 12 11 n m path1 certificate1 hn a

def path2 : List Nat := [34, 9, 38, 6, 41, 4, 40, 7, 37, 10, 36, 8, 39, 5, 43, 1, 46, 0, 44, 3, 42, 2, 45, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 13, 32, 12, 33, 11, 35]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate2 : FiniteAlpha.Certificate 10 6 7 path2 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair2 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨5,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨6,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 6 7 n m path2 certificate2 hn a

def path3 : List Nat := [34, 9, 38, 6, 41, 4, 40, 7, 37, 10, 36, 8, 39, 5, 43, 3, 42, 1, 46, 0, 44, 2, 45, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 13, 32, 12, 33, 11, 35]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate3 : FiniteAlpha.Certificate 10 4 5 path3 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair3 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨3,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨4,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 4 5 n m path3 certificate3 hn a

def path4 : List Nat := [34, 11, 33, 6, 38, 7, 40, 4, 44, 3, 41, 2, 45, 1, 46, 0, 42, 5, 39, 9, 37, 8, 43, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 13, 32, 12, 36, 10, 35]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate4 : FiniteAlpha.Certificate 10 8 9 path4 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair4 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨7,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨8,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 8 9 n m path4 certificate4 hn a

def path5 : List Nat := [34, 9, 37, 10, 36, 7, 40, 4, 43, 1, 46, 0, 44, 3, 41, 6, 38, 8, 39, 5, 42, 2, 45, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 13, 32, 12, 33, 11, 35]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate5 : FiniteAlpha.Certificate 10 12 13 path5 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair5 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨11,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨12,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 12 13 n m path5 certificate5 hn a

def path6 : List Nat := [34, 11, 33, 6, 41, 9, 37, 8, 38, 7, 40, 2, 46, 0, 45, 3, 39, 5, 42, 1, 44, 4, 43, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 13, 32, 12, 36, 10, 35]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate6 : FiniteAlpha.Certificate 10 10 11 path6 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair6 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨9,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨10,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 10 11 n m path6 certificate6 hn a

def path7 : List Nat := [34, 11, 33, 6, 40, 2, 45, 1, 46, 0, 42, 7, 39, 8, 38, 9, 37, 4, 41, 5, 44, 3, 43, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 13, 32, 12, 36, 10, 35]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate7 : FiniteAlpha.Certificate 10 14 15 path7 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair7 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨13,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨14,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 14 15 n m path7 certificate7 hn a

def path8 : List Nat := [34, 11, 33, 6, 45, 0, 46, 2, 42, 5, 37, 9, 38, 8, 39, 4, 40, 7, 41, 3, 44, 1, 43, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 13, 32, 12, 36, 10, 35]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate8 : FiniteAlpha.Certificate 10 18 17 path8 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair8 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨17,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨16,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 18 17 n m path8 certificate8 hn a

def path9 : List Nat := [35, 10, 36, 9, 37, 8, 38, 7, 39, 6, 40, 5, 41, 4, 42, 3, 43, 2, 44, 1, 45, 0, 46, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 13, 32, 12, 33, 11, 34]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate9 : FiniteAlpha.Certificate 10 2 1 path9 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair9 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨1,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨0,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 2 1 n m path9 certificate9 hn a

def path10 : List Nat := [34, 11, 33, 6, 41, 3, 46, 0, 45, 1, 42, 2, 44, 7, 39, 5, 38, 8, 37, 9, 40, 4, 43, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 13, 32, 12, 36, 10, 35]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate10 : FiniteAlpha.Certificate 10 16 17 path10 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair10 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨15,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨16,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 16 17 n m path10 certificate10 hn a

def path11 : List Nat := [35, 3, 45, 0, 46, 2, 39, 12, 33, 9, 37, 8, 38, 7, 40, 6, 41, 5, 43, 4, 44, 1, 42, 22, 23, 21, 24, 20, 25, 19, 26, 18, 27, 17, 28, 16, 29, 15, 30, 14, 31, 13, 32, 10, 36, 11, 34]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate11 : FiniteAlpha.Certificate 10 20 19 path11 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair11 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨19,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨18,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 20 19 n m path11 certificate11 hn a

def path12 : List Nat := [44, 0, 46, 1, 42, 4, 39, 5, 41, 2, 45, 3, 43, 6, 37, 12, 33, 13, 29, 17, 28, 19, 27, 22, 23, 21, 24, 20, 26, 16, 30, 15, 34, 11, 35, 9, 36, 7, 40, 8, 38, 10, 32, 14, 31, 18, 25]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate12 : FiniteAlpha.Certificate 10 22 21 path12 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair12 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨21,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat, Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨20,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 10 22 21 n m path12 certificate12 hn a

end GracefulBoundary.K23Packets
