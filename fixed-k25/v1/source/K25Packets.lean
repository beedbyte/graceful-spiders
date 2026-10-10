import FiniteAlphaTransfer
namespace GracefulBoundary.K25Packets

def path0 : List Nat := [42, 4, 50, 0, 49, 1, 48, 11, 37, 10, 38, 21, 30, 17, 29, 22, 26, 20, 31, 16, 32, 18, 28, 23, 25, 24, 27, 19, 40, 6, 45, 5, 46, 3, 47, 2, 44, 13, 35, 12, 36, 7, 43, 8, 41, 9, 39, 14, 34, 15, 33]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate0 : FiniteAlpha.Certificate 11 22 23 path0 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair0 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨21,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨22,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 22 23 n m path0 certificate0 hn a

def path1 : List Nat := [39, 11, 40, 10, 41, 9, 42, 8, 43, 7, 44, 6, 45, 5, 46, 4, 47, 3, 48, 2, 49, 1, 50, 0, 27, 24, 25, 23, 29, 22, 26, 21, 31, 20, 28, 19, 32, 18, 30, 15, 35, 16, 34, 17, 33, 12, 38, 13, 37, 14, 36]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate1 : FiniteAlpha.Certificate 11 2 3 path1 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair1 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨1,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨2,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 2 3 n m path1 certificate1 hn a

def path2 : List Nat := [37, 12, 36, 7, 45, 4, 43, 8, 41, 9, 40, 10, 44, 2, 49, 1, 50, 0, 46, 6, 42, 5, 48, 3, 47, 24, 25, 23, 26, 22, 27, 21, 28, 20, 29, 19, 30, 18, 31, 17, 32, 16, 33, 15, 34, 14, 35, 13, 39, 11, 38]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate2 : FiniteAlpha.Certificate 11 8 9 path2 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair2 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨7,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨8,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 8 9 n m path2 certificate2 hn a

def path3 : List Nat := [37, 10, 39, 11, 41, 9, 40, 7, 44, 4, 47, 1, 50, 0, 48, 3, 45, 6, 42, 8, 43, 5, 46, 2, 49, 24, 25, 23, 26, 22, 27, 21, 28, 20, 29, 19, 30, 18, 31, 17, 32, 16, 33, 15, 34, 14, 35, 13, 36, 12, 38]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate3 : FiniteAlpha.Certificate 11 12 13 path3 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair3 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨11,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨12,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 12 13 n m path3 certificate3 hn a

def path4 : List Nat := [37, 10, 41, 7, 44, 4, 47, 1, 50, 0, 48, 3, 45, 6, 42, 9, 39, 11, 40, 8, 43, 5, 46, 2, 49, 24, 25, 23, 26, 22, 27, 21, 28, 20, 29, 19, 30, 18, 31, 17, 32, 16, 33, 15, 34, 14, 35, 13, 36, 12, 38]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate4 : FiniteAlpha.Certificate 11 16 17 path4 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair4 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨15,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨16,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 16 17 n m path4 certificate4 hn a

def path5 : List Nat := [37, 12, 36, 7, 44, 8, 42, 9, 41, 10, 40, 5, 43, 3, 46, 4, 48, 2, 49, 1, 50, 0, 45, 6, 47, 24, 25, 23, 26, 22, 27, 21, 28, 20, 29, 19, 30, 18, 31, 17, 32, 16, 33, 15, 34, 14, 35, 13, 39, 11, 38]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate5 : FiniteAlpha.Certificate 11 4 5 path5 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair5 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨3,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨4,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 4 5 n m path5 certificate5 hn a

def path6 : List Nat := [37, 12, 36, 7, 42, 8, 44, 6, 45, 4, 41, 9, 40, 10, 43, 3, 46, 1, 50, 0, 48, 2, 49, 5, 47, 24, 25, 23, 26, 22, 27, 21, 28, 20, 29, 19, 30, 18, 31, 17, 32, 16, 33, 15, 34, 14, 35, 13, 39, 11, 38]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate6 : FiniteAlpha.Certificate 11 6 7 path6 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair6 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨5,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨6,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 6 7 n m path6 certificate6 hn a

def path7 : List Nat := [37, 12, 36, 7, 41, 8, 44, 9, 40, 10, 42, 4, 46, 1, 50, 0, 48, 5, 45, 6, 43, 2, 49, 3, 47, 24, 25, 23, 26, 22, 27, 21, 28, 20, 29, 19, 30, 18, 31, 17, 32, 16, 33, 15, 34, 14, 35, 13, 39, 11, 38]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate7 : FiniteAlpha.Certificate 11 10 11 path7 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair7 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨9,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨10,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 10 11 n m path7 certificate7 hn a

def path8 : List Nat := [37, 12, 36, 7, 43, 8, 45, 2, 49, 1, 50, 0, 46, 5, 44, 4, 42, 9, 41, 10, 40, 6, 48, 3, 47, 24, 25, 23, 26, 22, 27, 21, 28, 20, 29, 19, 30, 18, 31, 17, 32, 16, 33, 15, 34, 14, 35, 13, 39, 11, 38]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate8 : FiniteAlpha.Certificate 11 14 15 path8 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair8 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨13,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨14,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 14 15 n m path8 certificate8 hn a

def path9 : List Nat := [37, 12, 36, 7, 43, 8, 46, 0, 50, 1, 49, 2, 44, 4, 45, 6, 40, 10, 41, 9, 42, 5, 48, 3, 47, 24, 25, 23, 26, 22, 27, 21, 28, 20, 29, 19, 30, 18, 31, 17, 32, 16, 33, 15, 34, 14, 35, 13, 39, 11, 38]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate9 : FiniteAlpha.Certificate 11 18 17 path9 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair9 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨17,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨16,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 18 17 n m path9 certificate9 hn a

def path10 : List Nat := [38, 11, 39, 10, 40, 9, 41, 8, 42, 7, 43, 6, 44, 5, 45, 4, 46, 3, 47, 2, 48, 1, 49, 0, 50, 24, 25, 23, 26, 22, 27, 21, 28, 20, 29, 19, 30, 18, 31, 17, 32, 16, 33, 15, 34, 14, 35, 13, 36, 12, 37]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate10 : FiniteAlpha.Certificate 11 2 1 path10 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair10 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨1,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨0,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 2 1 n m path10 certificate10 hn a

def path11 : List Nat := [28, 16, 39, 6, 48, 0, 50, 1, 45, 7, 43, 4, 44, 9, 41, 10, 40, 12, 36, 14, 31, 20, 30, 21, 26, 24, 25, 22, 29, 23, 27, 19, 32, 18, 33, 17, 35, 15, 34, 13, 38, 11, 37, 8, 42, 5, 46, 3, 49, 2, 47]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate11 : FiniteAlpha.Certificate 11 20 19 path11 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair11 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨19,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨18,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 20 19 n m path11 certificate11 hn a

def path12 : List Nat := [31, 12, 49, 0, 50, 2, 46, 5, 45, 3, 48, 1, 47, 4, 43, 16, 34, 17, 33, 18, 32, 20, 28, 23, 25, 24, 27, 21, 30, 19, 29, 22, 26, 13, 37, 11, 36, 14, 35, 15, 38, 10, 39, 9, 40, 8, 41, 7, 42, 6, 44]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate12 : FiniteAlpha.Certificate 11 22 21 path12 := by
  unfold FiniteAlpha.Certificate GenericPathCertificate
  decide

theorem pair12 (n m : Nat) (hn : 2≤n) (a : Fin n) :
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨21,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 25 → Nat, Graceful (spiderGraph n m 25) (n*25+m) f ∧ f (.arm a ⟨20,by decide⟩)=0) :=
  FiniteAlpha.prescribed_zero 11 22 21 n m path12 certificate12 hn a

end GracefulBoundary.K25Packets
