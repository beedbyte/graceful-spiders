import RootedWords7
import RootedGraft
namespace GracefulBoundary.Rooted71

def selectedPoint (d : Nat) (hd : 1≤d ∧ d≤70) (right : Bool) : Fin 143 :=
  if right then rightPoint d hd else leftPoint d hd

theorem packet1 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 1 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 1 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word0,valid0,?_⟩
    decide
  · refine ⟨word0.reverse,reverseValid0,?_⟩
    decide

theorem packet2 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 2 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 2 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word1,valid1,?_⟩
    decide
  · refine ⟨word1.reverse,reverseValid1,?_⟩
    decide

theorem packet3 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 3 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 3 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word1,valid1,?_⟩
    decide
  · refine ⟨word1.reverse,reverseValid1,?_⟩
    decide

theorem packet4 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 4 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 4 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word2,valid2,?_⟩
    decide
  · refine ⟨word2.reverse,reverseValid2,?_⟩
    decide

theorem packet5 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 5 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 5 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word2,valid2,?_⟩
    decide
  · refine ⟨word2.reverse,reverseValid2,?_⟩
    decide

theorem packet6 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 6 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 6 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word3,valid3,?_⟩
    decide
  · refine ⟨word3.reverse,reverseValid3,?_⟩
    decide

theorem packet7 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 7 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 7 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word3,valid3,?_⟩
    decide
  · refine ⟨word3.reverse,reverseValid3,?_⟩
    decide

theorem packet8 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 8 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 8 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word4,valid4,?_⟩
    decide
  · refine ⟨word4.reverse,reverseValid4,?_⟩
    decide

theorem packet9 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 9 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 9 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word4,valid4,?_⟩
    decide
  · refine ⟨word4.reverse,reverseValid4,?_⟩
    decide

theorem packet10 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 10 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 10 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word5,valid5,?_⟩
    decide
  · refine ⟨word5.reverse,reverseValid5,?_⟩
    decide

theorem packet11 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 11 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 11 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word5,valid5,?_⟩
    decide
  · refine ⟨word5.reverse,reverseValid5,?_⟩
    decide

theorem packet12 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 12 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 12 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word6,valid6,?_⟩
    decide
  · refine ⟨word6.reverse,reverseValid6,?_⟩
    decide

theorem packet13 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 13 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 13 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word6,valid6,?_⟩
    decide
  · refine ⟨word6.reverse,reverseValid6,?_⟩
    decide

theorem packet14 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 14 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 14 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word7,valid7,?_⟩
    decide
  · refine ⟨word7.reverse,reverseValid7,?_⟩
    decide

theorem packet15 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 15 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 15 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word7,valid7,?_⟩
    decide
  · refine ⟨word7.reverse,reverseValid7,?_⟩
    decide

theorem packet16 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 16 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 16 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word8,valid8,?_⟩
    decide
  · refine ⟨word8.reverse,reverseValid8,?_⟩
    decide

theorem packet17 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 17 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 17 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word8,valid8,?_⟩
    decide
  · refine ⟨word8.reverse,reverseValid8,?_⟩
    decide

theorem packet18 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 18 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 18 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word9,valid9,?_⟩
    decide
  · refine ⟨word9.reverse,reverseValid9,?_⟩
    decide

theorem packet19 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 19 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 19 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word9,valid9,?_⟩
    decide
  · refine ⟨word9.reverse,reverseValid9,?_⟩
    decide

theorem packet20 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 20 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 20 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word10,valid10,?_⟩
    decide
  · refine ⟨word10.reverse,reverseValid10,?_⟩
    decide

theorem packet21 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 21 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 21 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word10,valid10,?_⟩
    decide
  · refine ⟨word10.reverse,reverseValid10,?_⟩
    decide

theorem packet22 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 22 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 22 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word11,valid11,?_⟩
    decide
  · refine ⟨word11.reverse,reverseValid11,?_⟩
    decide

theorem packet23 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 23 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 23 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word11,valid11,?_⟩
    decide
  · refine ⟨word11.reverse,reverseValid11,?_⟩
    decide

theorem packet24 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 24 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 24 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word12,valid12,?_⟩
    decide
  · refine ⟨word12.reverse,reverseValid12,?_⟩
    decide

theorem packet25 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 25 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 25 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word12,valid12,?_⟩
    decide
  · refine ⟨word12.reverse,reverseValid12,?_⟩
    decide

theorem packet26 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 26 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 26 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word13,valid13,?_⟩
    decide
  · refine ⟨word13.reverse,reverseValid13,?_⟩
    decide

theorem packet27 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 27 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 27 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word13,valid13,?_⟩
    decide
  · refine ⟨word13.reverse,reverseValid13,?_⟩
    decide

theorem packet28 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 28 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 28 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word14,valid14,?_⟩
    decide
  · refine ⟨word14.reverse,reverseValid14,?_⟩
    decide

theorem packet29 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 29 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 29 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word14,valid14,?_⟩
    decide
  · refine ⟨word14.reverse,reverseValid14,?_⟩
    decide

theorem packet30 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 30 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 30 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word15,valid15,?_⟩
    decide
  · refine ⟨word15.reverse,reverseValid15,?_⟩
    decide

theorem packet31 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 31 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 31 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word15,valid15,?_⟩
    decide
  · refine ⟨word15.reverse,reverseValid15,?_⟩
    decide

theorem packet32 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 32 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 32 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word16,valid16,?_⟩
    decide
  · refine ⟨word16.reverse,reverseValid16,?_⟩
    decide

theorem packet33 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 33 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 33 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word16,valid16,?_⟩
    decide
  · refine ⟨word16.reverse,reverseValid16,?_⟩
    decide

theorem packet34 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 34 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 34 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word17,valid17,?_⟩
    decide
  · refine ⟨word17.reverse,reverseValid17,?_⟩
    decide

theorem packet35 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 35 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 35 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word17,valid17,?_⟩
    decide
  · refine ⟨word17.reverse,reverseValid17,?_⟩
    decide

theorem packet36 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 36 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 36 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word18,valid18,?_⟩
    decide
  · refine ⟨word18.reverse,reverseValid18,?_⟩
    decide

theorem packet37 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 37 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 37 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word18,valid18,?_⟩
    decide
  · refine ⟨word18.reverse,reverseValid18,?_⟩
    decide

theorem packet38 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 38 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 38 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word19,valid19,?_⟩
    decide
  · refine ⟨word19.reverse,reverseValid19,?_⟩
    decide

theorem packet39 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 39 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 39 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word19,valid19,?_⟩
    decide
  · refine ⟨word19.reverse,reverseValid19,?_⟩
    decide

theorem packet40 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 40 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 40 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word20,valid20,?_⟩
    decide
  · refine ⟨word20.reverse,reverseValid20,?_⟩
    decide

theorem packet41 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 41 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 41 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word20,valid20,?_⟩
    decide
  · refine ⟨word20.reverse,reverseValid20,?_⟩
    decide

theorem packet42 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 42 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 42 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word21,valid21,?_⟩
    decide
  · refine ⟨word21.reverse,reverseValid21,?_⟩
    decide

theorem packet43 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 43 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 43 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word21,valid21,?_⟩
    decide
  · refine ⟨word21.reverse,reverseValid21,?_⟩
    decide

theorem packet44 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 44 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 44 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word22,valid22,?_⟩
    decide
  · refine ⟨word22.reverse,reverseValid22,?_⟩
    decide

theorem packet45 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 45 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 45 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word22,valid22,?_⟩
    decide
  · refine ⟨word22.reverse,reverseValid22,?_⟩
    decide

theorem packet46 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 46 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 46 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word23,valid23,?_⟩
    decide
  · refine ⟨word23.reverse,reverseValid23,?_⟩
    decide

theorem packet47 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 47 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 47 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word23,valid23,?_⟩
    decide
  · refine ⟨word23.reverse,reverseValid23,?_⟩
    decide

theorem packet48 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 48 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 48 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word24,valid24,?_⟩
    decide
  · refine ⟨word24.reverse,reverseValid24,?_⟩
    decide

theorem packet49 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 49 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 49 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word24,valid24,?_⟩
    decide
  · refine ⟨word24.reverse,reverseValid24,?_⟩
    decide

theorem packet50 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 50 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 50 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word25,valid25,?_⟩
    decide
  · refine ⟨word25.reverse,reverseValid25,?_⟩
    decide

theorem packet51 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 51 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 51 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word25,valid25,?_⟩
    decide
  · refine ⟨word25.reverse,reverseValid25,?_⟩
    decide

theorem packet52 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 52 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 52 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word26,valid26,?_⟩
    decide
  · refine ⟨word26.reverse,reverseValid26,?_⟩
    decide

theorem packet53 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 53 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 53 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word26,valid26,?_⟩
    decide
  · refine ⟨word26.reverse,reverseValid26,?_⟩
    decide

theorem packet54 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 54 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 54 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word27,valid27,?_⟩
    decide
  · refine ⟨word27.reverse,reverseValid27,?_⟩
    decide

theorem packet55 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 55 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 55 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word27,valid27,?_⟩
    decide
  · refine ⟨word27.reverse,reverseValid27,?_⟩
    decide

theorem packet56 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 56 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 56 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word28,valid28,?_⟩
    decide
  · refine ⟨word28.reverse,reverseValid28,?_⟩
    decide

theorem packet57 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 57 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 57 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word28,valid28,?_⟩
    decide
  · refine ⟨word28.reverse,reverseValid28,?_⟩
    decide

theorem packet58 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 58 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 58 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word29,valid29,?_⟩
    decide
  · refine ⟨word29.reverse,reverseValid29,?_⟩
    decide

theorem packet59 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 59 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 59 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word30,valid30,?_⟩
    decide
  · refine ⟨word30.reverse,reverseValid30,?_⟩
    decide

theorem packet60 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 60 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 60 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word30,valid30,?_⟩
    decide
  · refine ⟨word30.reverse,reverseValid30,?_⟩
    decide

theorem packet61 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 61 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 61 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word31,valid31,?_⟩
    decide
  · refine ⟨word31.reverse,reverseValid31,?_⟩
    decide

theorem packet62 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 62 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 62 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word31,valid31,?_⟩
    decide
  · refine ⟨word31.reverse,reverseValid31,?_⟩
    decide

theorem packet63 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 63 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 63 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word32,valid32,?_⟩
    decide
  · refine ⟨word32.reverse,reverseValid32,?_⟩
    decide

theorem packet64 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 64 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 64 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word32,valid32,?_⟩
    decide
  · refine ⟨word32.reverse,reverseValid32,?_⟩
    decide

theorem packet65 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 65 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 65 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word33,valid33,?_⟩
    decide
  · refine ⟨word33.reverse,reverseValid33,?_⟩
    decide

theorem packet66 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 66 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 66 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word33,valid33,?_⟩
    decide
  · refine ⟨word33.reverse,reverseValid33,?_⟩
    decide

theorem packet67 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 67 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 67 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word34,valid34,?_⟩
    decide
  · refine ⟨word34.reverse,reverseValid34,?_⟩
    decide

theorem packet68 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 68 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 68 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word35,valid35,?_⟩
    decide
  · refine ⟨word35.reverse,reverseValid35,?_⟩
    decide

theorem packet69 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 69 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 69 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word36,valid36,?_⟩
    decide
  · refine ⟨word36.reverse,reverseValid36,?_⟩
    decide

theorem packet70 (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint 70 ⟨by omega, by omega⟩ right).val]?=some 0 ∨
       w[(selectedPoint 70 ⟨by omega, by omega⟩ right).val]?=some 142) := by
  cases right
  · refine ⟨word36,valid36,?_⟩
    decide
  · refine ⟨word36.reverse,reverseValid36,?_⟩
    decide

theorem all_packets (d : Nat) (hd : 1≤d ∧ d≤70) (right : Bool) :
    ∃ w : List Nat, GenericPathCertificate 34 w ∧
      (w[(selectedPoint d hd right).val]?=some 0 ∨
       w[(selectedPoint d hd right).val]?=some 142) := by
  have hsplit : d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=5 ∨ d=6 ∨ d=7 ∨ d=8 ∨ d=9 ∨ d=10 ∨ d=11 ∨ d=12 ∨ d=13 ∨ d=14 ∨ d=15 ∨ d=16 ∨ d=17 ∨ d=18 ∨ d=19 ∨ d=20 ∨ d=21 ∨ d=22 ∨ d=23 ∨ d=24 ∨ d=25 ∨ d=26 ∨ d=27 ∨ d=28 ∨ d=29 ∨ d=30 ∨ d=31 ∨ d=32 ∨ d=33 ∨ d=34 ∨ d=35 ∨ d=36 ∨ d=37 ∨ d=38 ∨ d=39 ∨ d=40 ∨ d=41 ∨ d=42 ∨ d=43 ∨ d=44 ∨ d=45 ∨ d=46 ∨ d=47 ∨ d=48 ∨ d=49 ∨ d=50 ∨ d=51 ∨ d=52 ∨ d=53 ∨ d=54 ∨ d=55 ∨ d=56 ∨ d=57 ∨ d=58 ∨ d=59 ∨ d=60 ∨ d=61 ∨ d=62 ∨ d=63 ∨ d=64 ∨ d=65 ∨ d=66 ∨ d=67 ∨ d=68 ∨ d=69 ∨ d=70 := by omega
  rcases hsplit with h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60|h61|h62|h63|h64|h65|h66|h67|h68|h69|h70
  · subst d
    simpa only using packet1 right
  · subst d
    simpa only using packet2 right
  · subst d
    simpa only using packet3 right
  · subst d
    simpa only using packet4 right
  · subst d
    simpa only using packet5 right
  · subst d
    simpa only using packet6 right
  · subst d
    simpa only using packet7 right
  · subst d
    simpa only using packet8 right
  · subst d
    simpa only using packet9 right
  · subst d
    simpa only using packet10 right
  · subst d
    simpa only using packet11 right
  · subst d
    simpa only using packet12 right
  · subst d
    simpa only using packet13 right
  · subst d
    simpa only using packet14 right
  · subst d
    simpa only using packet15 right
  · subst d
    simpa only using packet16 right
  · subst d
    simpa only using packet17 right
  · subst d
    simpa only using packet18 right
  · subst d
    simpa only using packet19 right
  · subst d
    simpa only using packet20 right
  · subst d
    simpa only using packet21 right
  · subst d
    simpa only using packet22 right
  · subst d
    simpa only using packet23 right
  · subst d
    simpa only using packet24 right
  · subst d
    simpa only using packet25 right
  · subst d
    simpa only using packet26 right
  · subst d
    simpa only using packet27 right
  · subst d
    simpa only using packet28 right
  · subst d
    simpa only using packet29 right
  · subst d
    simpa only using packet30 right
  · subst d
    simpa only using packet31 right
  · subst d
    simpa only using packet32 right
  · subst d
    simpa only using packet33 right
  · subst d
    simpa only using packet34 right
  · subst d
    simpa only using packet35 right
  · subst d
    simpa only using packet36 right
  · subst d
    simpa only using packet37 right
  · subst d
    simpa only using packet38 right
  · subst d
    simpa only using packet39 right
  · subst d
    simpa only using packet40 right
  · subst d
    simpa only using packet41 right
  · subst d
    simpa only using packet42 right
  · subst d
    simpa only using packet43 right
  · subst d
    simpa only using packet44 right
  · subst d
    simpa only using packet45 right
  · subst d
    simpa only using packet46 right
  · subst d
    simpa only using packet47 right
  · subst d
    simpa only using packet48 right
  · subst d
    simpa only using packet49 right
  · subst d
    simpa only using packet50 right
  · subst d
    simpa only using packet51 right
  · subst d
    simpa only using packet52 right
  · subst d
    simpa only using packet53 right
  · subst d
    simpa only using packet54 right
  · subst d
    simpa only using packet55 right
  · subst d
    simpa only using packet56 right
  · subst d
    simpa only using packet57 right
  · subst d
    simpa only using packet58 right
  · subst d
    simpa only using packet59 right
  · subst d
    simpa only using packet60 right
  · subst d
    simpa only using packet61 right
  · subst d
    simpa only using packet62 right
  · subst d
    simpa only using packet63 right
  · subst d
    simpa only using packet64 right
  · subst d
    simpa only using packet65 right
  · subst d
    simpa only using packet66 right
  · subst d
    simpa only using packet67 right
  · subst d
    simpa only using packet68 right
  · subst d
    simpa only using packet69 right
  · subst d
    simpa only using packet70 right

end GracefulBoundary.Rooted71
