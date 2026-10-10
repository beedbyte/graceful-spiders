import Q24Rooted
import K119Catalog6
namespace GracefulBoundary.K119Rooted
open Rooted71
theorem packet_extreme (z q d : Nat) (w : List Nat)
    (hc : FiniteAlpha.Certificate 58 z q w) (hd : d=z ∨ d=q) :
    GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  rcases hc with ⟨_,_,_,_,hg,hz,hm⟩
  rcases hd with rfl|rfl
  · exact ⟨hg,Or.inl hz⟩
  · exact ⟨hg,Or.inr hm⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem catalog_1_10 (d : Nat) (hd : 1≤d ∧ d≤10) :
    ∃ w : List Nat, GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  have hs : d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=5 ∨ d=6 ∨ d=7 ∨ d=8 ∨ d=9 ∨ d=10 := by omega
  rcases hs with h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
  · subst d
    exact ⟨K119Catalog.path0,packet_extreme 2 1 1 K119Catalog.path0
      K119Catalog.packet0 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path1,packet_extreme 2 3 2 K119Catalog.path1
      K119Catalog.packet1 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path1,packet_extreme 2 3 3 K119Catalog.path1
      K119Catalog.packet1 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path2,packet_extreme 4 5 4 K119Catalog.path2
      K119Catalog.packet2 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path2,packet_extreme 4 5 5 K119Catalog.path2
      K119Catalog.packet2 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path3,packet_extreme 6 7 6 K119Catalog.path3
      K119Catalog.packet3 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path3,packet_extreme 6 7 7 K119Catalog.path3
      K119Catalog.packet3 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path4,packet_extreme 8 9 8 K119Catalog.path4
      K119Catalog.packet4 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path4,packet_extreme 8 9 9 K119Catalog.path4
      K119Catalog.packet4 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path5,packet_extreme 10 11 10 K119Catalog.path5
      K119Catalog.packet5 (Or.inl rfl)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem catalog_11_20 (d : Nat) (hd : 11≤d ∧ d≤20) :
    ∃ w : List Nat, GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  have hs : d=11 ∨ d=12 ∨ d=13 ∨ d=14 ∨ d=15 ∨ d=16 ∨ d=17 ∨ d=18 ∨ d=19 ∨ d=20 := by omega
  rcases hs with h11|h12|h13|h14|h15|h16|h17|h18|h19|h20
  · subst d
    exact ⟨K119Catalog.path5,packet_extreme 10 11 11 K119Catalog.path5
      K119Catalog.packet5 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path6,packet_extreme 12 13 12 K119Catalog.path6
      K119Catalog.packet6 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path6,packet_extreme 12 13 13 K119Catalog.path6
      K119Catalog.packet6 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path7,packet_extreme 14 15 14 K119Catalog.path7
      K119Catalog.packet7 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path7,packet_extreme 14 15 15 K119Catalog.path7
      K119Catalog.packet7 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path8,packet_extreme 16 17 16 K119Catalog.path8
      K119Catalog.packet8 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path8,packet_extreme 16 17 17 K119Catalog.path8
      K119Catalog.packet8 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path9,packet_extreme 18 19 18 K119Catalog.path9
      K119Catalog.packet9 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path9,packet_extreme 18 19 19 K119Catalog.path9
      K119Catalog.packet9 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path10,packet_extreme 20 21 20 K119Catalog.path10
      K119Catalog.packet10 (Or.inl rfl)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem catalog_21_30 (d : Nat) (hd : 21≤d ∧ d≤30) :
    ∃ w : List Nat, GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  have hs : d=21 ∨ d=22 ∨ d=23 ∨ d=24 ∨ d=25 ∨ d=26 ∨ d=27 ∨ d=28 ∨ d=29 ∨ d=30 := by omega
  rcases hs with h21|h22|h23|h24|h25|h26|h27|h28|h29|h30
  · subst d
    exact ⟨K119Catalog.path10,packet_extreme 20 21 21 K119Catalog.path10
      K119Catalog.packet10 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path11,packet_extreme 22 23 22 K119Catalog.path11
      K119Catalog.packet11 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path11,packet_extreme 22 23 23 K119Catalog.path11
      K119Catalog.packet11 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path12,packet_extreme 24 25 24 K119Catalog.path12
      K119Catalog.packet12 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path12,packet_extreme 24 25 25 K119Catalog.path12
      K119Catalog.packet12 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path13,packet_extreme 26 27 26 K119Catalog.path13
      K119Catalog.packet13 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path13,packet_extreme 26 27 27 K119Catalog.path13
      K119Catalog.packet13 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path14,packet_extreme 28 29 28 K119Catalog.path14
      K119Catalog.packet14 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path14,packet_extreme 28 29 29 K119Catalog.path14
      K119Catalog.packet14 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path15,packet_extreme 30 31 30 K119Catalog.path15
      K119Catalog.packet15 (Or.inl rfl)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem catalog_31_40 (d : Nat) (hd : 31≤d ∧ d≤40) :
    ∃ w : List Nat, GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  have hs : d=31 ∨ d=32 ∨ d=33 ∨ d=34 ∨ d=35 ∨ d=36 ∨ d=37 ∨ d=38 ∨ d=39 ∨ d=40 := by omega
  rcases hs with h31|h32|h33|h34|h35|h36|h37|h38|h39|h40
  · subst d
    exact ⟨K119Catalog.path15,packet_extreme 30 31 31 K119Catalog.path15
      K119Catalog.packet15 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path16,packet_extreme 32 33 32 K119Catalog.path16
      K119Catalog.packet16 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path16,packet_extreme 32 33 33 K119Catalog.path16
      K119Catalog.packet16 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path17,packet_extreme 34 35 34 K119Catalog.path17
      K119Catalog.packet17 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path17,packet_extreme 34 35 35 K119Catalog.path17
      K119Catalog.packet17 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path18,packet_extreme 36 37 36 K119Catalog.path18
      K119Catalog.packet18 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path18,packet_extreme 36 37 37 K119Catalog.path18
      K119Catalog.packet18 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path19,packet_extreme 38 39 38 K119Catalog.path19
      K119Catalog.packet19 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path19,packet_extreme 38 39 39 K119Catalog.path19
      K119Catalog.packet19 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path20,packet_extreme 40 41 40 K119Catalog.path20
      K119Catalog.packet20 (Or.inl rfl)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem catalog_41_50 (d : Nat) (hd : 41≤d ∧ d≤50) :
    ∃ w : List Nat, GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  have hs : d=41 ∨ d=42 ∨ d=43 ∨ d=44 ∨ d=45 ∨ d=46 ∨ d=47 ∨ d=48 ∨ d=49 ∨ d=50 := by omega
  rcases hs with h41|h42|h43|h44|h45|h46|h47|h48|h49|h50
  · subst d
    exact ⟨K119Catalog.path20,packet_extreme 40 41 41 K119Catalog.path20
      K119Catalog.packet20 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path21,packet_extreme 42 43 42 K119Catalog.path21
      K119Catalog.packet21 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path21,packet_extreme 42 43 43 K119Catalog.path21
      K119Catalog.packet21 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path22,packet_extreme 44 45 44 K119Catalog.path22
      K119Catalog.packet22 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path22,packet_extreme 44 45 45 K119Catalog.path22
      K119Catalog.packet22 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path23,packet_extreme 46 47 46 K119Catalog.path23
      K119Catalog.packet23 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path23,packet_extreme 46 47 47 K119Catalog.path23
      K119Catalog.packet23 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path24,packet_extreme 48 49 48 K119Catalog.path24
      K119Catalog.packet24 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path24,packet_extreme 48 49 49 K119Catalog.path24
      K119Catalog.packet24 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path25,packet_extreme 50 51 50 K119Catalog.path25
      K119Catalog.packet25 (Or.inl rfl)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem catalog_51_60 (d : Nat) (hd : 51≤d ∧ d≤60) :
    ∃ w : List Nat, GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  have hs : d=51 ∨ d=52 ∨ d=53 ∨ d=54 ∨ d=55 ∨ d=56 ∨ d=57 ∨ d=58 ∨ d=59 ∨ d=60 := by omega
  rcases hs with h51|h52|h53|h54|h55|h56|h57|h58|h59|h60
  · subst d
    exact ⟨K119Catalog.path25,packet_extreme 50 51 51 K119Catalog.path25
      K119Catalog.packet25 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path26,packet_extreme 52 53 52 K119Catalog.path26
      K119Catalog.packet26 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path26,packet_extreme 52 53 53 K119Catalog.path26
      K119Catalog.packet26 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path27,packet_extreme 54 55 54 K119Catalog.path27
      K119Catalog.packet27 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path27,packet_extreme 54 55 55 K119Catalog.path27
      K119Catalog.packet27 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path28,packet_extreme 56 57 56 K119Catalog.path28
      K119Catalog.packet28 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path28,packet_extreme 56 57 57 K119Catalog.path28
      K119Catalog.packet28 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path29,packet_extreme 58 59 58 K119Catalog.path29
      K119Catalog.packet29 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path29,packet_extreme 58 59 59 K119Catalog.path29
      K119Catalog.packet29 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path30,packet_extreme 60 61 60 K119Catalog.path30
      K119Catalog.packet30 (Or.inl rfl)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem catalog_61_70 (d : Nat) (hd : 61≤d ∧ d≤70) :
    ∃ w : List Nat, GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  have hs : d=61 ∨ d=62 ∨ d=63 ∨ d=64 ∨ d=65 ∨ d=66 ∨ d=67 ∨ d=68 ∨ d=69 ∨ d=70 := by omega
  rcases hs with h61|h62|h63|h64|h65|h66|h67|h68|h69|h70
  · subst d
    exact ⟨K119Catalog.path30,packet_extreme 60 61 61 K119Catalog.path30
      K119Catalog.packet30 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path31,packet_extreme 62 63 62 K119Catalog.path31
      K119Catalog.packet31 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path31,packet_extreme 62 63 63 K119Catalog.path31
      K119Catalog.packet31 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path32,packet_extreme 64 65 64 K119Catalog.path32
      K119Catalog.packet32 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path32,packet_extreme 64 65 65 K119Catalog.path32
      K119Catalog.packet32 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path33,packet_extreme 66 67 66 K119Catalog.path33
      K119Catalog.packet33 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path33,packet_extreme 66 67 67 K119Catalog.path33
      K119Catalog.packet33 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path34,packet_extreme 68 69 68 K119Catalog.path34
      K119Catalog.packet34 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path34,packet_extreme 68 69 69 K119Catalog.path34
      K119Catalog.packet34 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path35,packet_extreme 70 71 70 K119Catalog.path35
      K119Catalog.packet35 (Or.inl rfl)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem catalog_71_80 (d : Nat) (hd : 71≤d ∧ d≤80) :
    ∃ w : List Nat, GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  have hs : d=71 ∨ d=72 ∨ d=73 ∨ d=74 ∨ d=75 ∨ d=76 ∨ d=77 ∨ d=78 ∨ d=79 ∨ d=80 := by omega
  rcases hs with h71|h72|h73|h74|h75|h76|h77|h78|h79|h80
  · subst d
    exact ⟨K119Catalog.path35,packet_extreme 70 71 71 K119Catalog.path35
      K119Catalog.packet35 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path36,packet_extreme 72 73 72 K119Catalog.path36
      K119Catalog.packet36 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path36,packet_extreme 72 73 73 K119Catalog.path36
      K119Catalog.packet36 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path37,packet_extreme 74 75 74 K119Catalog.path37
      K119Catalog.packet37 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path37,packet_extreme 74 75 75 K119Catalog.path37
      K119Catalog.packet37 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path38,packet_extreme 76 77 76 K119Catalog.path38
      K119Catalog.packet38 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path38,packet_extreme 76 77 77 K119Catalog.path38
      K119Catalog.packet38 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path39,packet_extreme 78 79 78 K119Catalog.path39
      K119Catalog.packet39 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path39,packet_extreme 78 79 79 K119Catalog.path39
      K119Catalog.packet39 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path40,packet_extreme 80 81 80 K119Catalog.path40
      K119Catalog.packet40 (Or.inl rfl)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem catalog_81_90 (d : Nat) (hd : 81≤d ∧ d≤90) :
    ∃ w : List Nat, GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  have hs : d=81 ∨ d=82 ∨ d=83 ∨ d=84 ∨ d=85 ∨ d=86 ∨ d=87 ∨ d=88 ∨ d=89 ∨ d=90 := by omega
  rcases hs with h81|h82|h83|h84|h85|h86|h87|h88|h89|h90
  · subst d
    exact ⟨K119Catalog.path40,packet_extreme 80 81 81 K119Catalog.path40
      K119Catalog.packet40 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path41,packet_extreme 82 83 82 K119Catalog.path41
      K119Catalog.packet41 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path41,packet_extreme 82 83 83 K119Catalog.path41
      K119Catalog.packet41 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path42,packet_extreme 84 85 84 K119Catalog.path42
      K119Catalog.packet42 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path42,packet_extreme 84 85 85 K119Catalog.path42
      K119Catalog.packet42 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path43,packet_extreme 86 87 86 K119Catalog.path43
      K119Catalog.packet43 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path43,packet_extreme 86 87 87 K119Catalog.path43
      K119Catalog.packet43 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path44,packet_extreme 88 89 88 K119Catalog.path44
      K119Catalog.packet44 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path44,packet_extreme 88 89 89 K119Catalog.path44
      K119Catalog.packet44 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path45,packet_extreme 90 91 90 K119Catalog.path45
      K119Catalog.packet45 (Or.inl rfl)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem catalog_91_100 (d : Nat) (hd : 91≤d ∧ d≤100) :
    ∃ w : List Nat, GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  have hs : d=91 ∨ d=92 ∨ d=93 ∨ d=94 ∨ d=95 ∨ d=96 ∨ d=97 ∨ d=98 ∨ d=99 ∨ d=100 := by omega
  rcases hs with h91|h92|h93|h94|h95|h96|h97|h98|h99|h100
  · subst d
    exact ⟨K119Catalog.path45,packet_extreme 90 91 91 K119Catalog.path45
      K119Catalog.packet45 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path46,packet_extreme 92 91 92 K119Catalog.path46
      K119Catalog.packet46 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path47,packet_extreme 92 93 93 K119Catalog.path47
      K119Catalog.packet47 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path48,packet_extreme 94 93 94 K119Catalog.path48
      K119Catalog.packet48 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path49,packet_extreme 94 95 95 K119Catalog.path49
      K119Catalog.packet49 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path50,packet_extreme 96 97 96 K119Catalog.path50
      K119Catalog.packet50 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path50,packet_extreme 96 97 97 K119Catalog.path50
      K119Catalog.packet50 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path51,packet_extreme 98 97 98 K119Catalog.path51
      K119Catalog.packet51 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path52,packet_extreme 98 99 99 K119Catalog.path52
      K119Catalog.packet52 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path53,packet_extreme 100 99 100 K119Catalog.path53
      K119Catalog.packet53 (Or.inl rfl)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem catalog_101_110 (d : Nat) (hd : 101≤d ∧ d≤110) :
    ∃ w : List Nat, GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  have hs : d=101 ∨ d=102 ∨ d=103 ∨ d=104 ∨ d=105 ∨ d=106 ∨ d=107 ∨ d=108 ∨ d=109 ∨ d=110 := by omega
  rcases hs with h101|h102|h103|h104|h105|h106|h107|h108|h109|h110
  · subst d
    exact ⟨K119Catalog.path54,packet_extreme 102 101 101 K119Catalog.path54
      K119Catalog.packet54 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path54,packet_extreme 102 101 102 K119Catalog.path54
      K119Catalog.packet54 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path55,packet_extreme 102 103 103 K119Catalog.path55
      K119Catalog.packet55 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path56,packet_extreme 104 103 104 K119Catalog.path56
      K119Catalog.packet56 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path57,packet_extreme 106 105 105 K119Catalog.path57
      K119Catalog.packet57 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path57,packet_extreme 106 105 106 K119Catalog.path57
      K119Catalog.packet57 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path58,packet_extreme 108 107 107 K119Catalog.path58
      K119Catalog.packet58 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path58,packet_extreme 108 107 108 K119Catalog.path58
      K119Catalog.packet58 (Or.inl rfl)⟩
  · subst d
    exact ⟨K119Catalog.path59,packet_extreme 108 109 109 K119Catalog.path59
      K119Catalog.packet59 (Or.inr rfl)⟩
  · subst d
    exact ⟨K119Catalog.path60,packet_extreme 110 109 110 K119Catalog.path60
      K119Catalog.packet60 (Or.inl rfl)⟩

theorem catalog_extreme (d : Nat) (hd : 1≤d ∧ d≤110) :
    ∃ w : List Nat, GenericPathCertificate 58 w ∧
      (w[119-d]?=some 0 ∨ w[119-d]?=some 238) := by
  by_cases h10 : d≤10
  · exact catalog_1_10 d ⟨by omega,h10⟩
  by_cases h20 : d≤20
  · exact catalog_11_20 d ⟨by omega,h20⟩
  by_cases h30 : d≤30
  · exact catalog_21_30 d ⟨by omega,h30⟩
  by_cases h40 : d≤40
  · exact catalog_31_40 d ⟨by omega,h40⟩
  by_cases h50 : d≤50
  · exact catalog_41_50 d ⟨by omega,h50⟩
  by_cases h60 : d≤60
  · exact catalog_51_60 d ⟨by omega,h60⟩
  by_cases h70 : d≤70
  · exact catalog_61_70 d ⟨by omega,h70⟩
  by_cases h80 : d≤80
  · exact catalog_71_80 d ⟨by omega,h80⟩
  by_cases h90 : d≤90
  · exact catalog_81_90 d ⟨by omega,h90⟩
  by_cases h100 : d≤100
  · exact catalog_91_100 d ⟨by omega,h100⟩
  exact catalog_101_110 d ⟨by omega,hd.2⟩

/-- Separate zero labelings at both actual named new-arm vertices, depths1..110. -/
theorem interior {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hd : 1≤d ∧ d≤110) :
    Q24Rooted.ZeroAt H root Q 58 ⟨119-d,by omega⟩ ∧
    Q24Rooted.ZeroAt H root Q 58 ⟨119+d,by omega⟩ := by
  obtain ⟨w,hw,hx⟩ := catalog_extreme d hd
  exact ⟨Q24Rooted.rooted_left H root g Q 58 d hg hroot w hw (by omega) hx,
    Q24Rooted.rooted_right H root g Q 58 d hg hroot w hw (by omega) hx⟩
end GracefulBoundary.K119Rooted
