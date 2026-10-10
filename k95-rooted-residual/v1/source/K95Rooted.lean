import Q24Rooted
import K95Catalog8

namespace GracefulBoundary.K95Rooted

open Rooted71

theorem packet_extreme (z q d : Nat) (w : List Nat)
    (hc : FiniteAlpha.Certificate 46 z q w) (hd : d=z ∨ d=q) :
    GenericPathCertificate 46 w ∧
      (w[95-d]?=some 0 ∨ w[95-d]?=some 190) := by
  rcases hc with ⟨_,_,_,_,hg,hz,hm⟩
  rcases hd with rfl|rfl
  · exact ⟨hg,Or.inl hz⟩
  · exact ⟨hg,Or.inr hm⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem catalog_extreme (d : Nat) (hd : 1≤d ∧ d≤94) :
    ∃ w : List Nat, GenericPathCertificate 46 w ∧
      (w[95-d]?=some 0 ∨ w[95-d]?=some 190) := by
  have hsplit : d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=5 ∨ d=6 ∨ d=7 ∨ d=8 ∨ d=9 ∨ d=10 ∨ d=11 ∨ d=12 ∨ d=13 ∨ d=14 ∨ d=15 ∨ d=16 ∨ d=17 ∨ d=18 ∨ d=19 ∨ d=20 ∨ d=21 ∨ d=22 ∨ d=23 ∨ d=24 ∨ d=25 ∨ d=26 ∨ d=27 ∨ d=28 ∨ d=29 ∨ d=30 ∨ d=31 ∨ d=32 ∨ d=33 ∨ d=34 ∨ d=35 ∨ d=36 ∨ d=37 ∨ d=38 ∨ d=39 ∨ d=40 ∨ d=41 ∨ d=42 ∨ d=43 ∨ d=44 ∨ d=45 ∨ d=46 ∨ d=47 ∨ d=48 ∨ d=49 ∨ d=50 ∨ d=51 ∨ d=52 ∨ d=53 ∨ d=54 ∨ d=55 ∨ d=56 ∨ d=57 ∨ d=58 ∨ d=59 ∨ d=60 ∨ d=61 ∨ d=62 ∨ d=63 ∨ d=64 ∨ d=65 ∨ d=66 ∨ d=67 ∨ d=68 ∨ d=69 ∨ d=70 ∨ d=71 ∨ d=72 ∨ d=73 ∨ d=74 ∨ d=75 ∨ d=76 ∨ d=77 ∨ d=78 ∨ d=79 ∨ d=80 ∨ d=81 ∨ d=82 ∨ d=83 ∨ d=84 ∨ d=85 ∨ d=86 ∨ d=87 ∨ d=88 ∨ d=89 ∨ d=90 ∨ d=91 ∨ d=92 ∨ d=93 ∨ d=94 := by omega
  rcases hsplit with h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60|h61|h62|h63|h64|h65|h66|h67|h68|h69|h70|h71|h72|h73|h74|h75|h76|h77|h78|h79|h80|h81|h82|h83|h84|h85|h86|h87|h88|h89|h90|h91|h92|h93|h94
  · subst d
    exact ⟨K95Catalog.path0, packet_extreme 2 1 1 K95Catalog.path0
      K95Catalog.packet0 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path1, packet_extreme 2 3 2 K95Catalog.path1
      K95Catalog.packet1 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path1, packet_extreme 2 3 3 K95Catalog.path1
      K95Catalog.packet1 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path2, packet_extreme 4 5 4 K95Catalog.path2
      K95Catalog.packet2 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path2, packet_extreme 4 5 5 K95Catalog.path2
      K95Catalog.packet2 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path3, packet_extreme 6 7 6 K95Catalog.path3
      K95Catalog.packet3 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path3, packet_extreme 6 7 7 K95Catalog.path3
      K95Catalog.packet3 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path4, packet_extreme 8 9 8 K95Catalog.path4
      K95Catalog.packet4 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path4, packet_extreme 8 9 9 K95Catalog.path4
      K95Catalog.packet4 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path5, packet_extreme 10 11 10 K95Catalog.path5
      K95Catalog.packet5 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path5, packet_extreme 10 11 11 K95Catalog.path5
      K95Catalog.packet5 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path6, packet_extreme 12 13 12 K95Catalog.path6
      K95Catalog.packet6 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path6, packet_extreme 12 13 13 K95Catalog.path6
      K95Catalog.packet6 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path7, packet_extreme 14 15 14 K95Catalog.path7
      K95Catalog.packet7 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path7, packet_extreme 14 15 15 K95Catalog.path7
      K95Catalog.packet7 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path8, packet_extreme 16 17 16 K95Catalog.path8
      K95Catalog.packet8 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path8, packet_extreme 16 17 17 K95Catalog.path8
      K95Catalog.packet8 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path9, packet_extreme 18 19 18 K95Catalog.path9
      K95Catalog.packet9 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path9, packet_extreme 18 19 19 K95Catalog.path9
      K95Catalog.packet9 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path10, packet_extreme 20 21 20 K95Catalog.path10
      K95Catalog.packet10 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path10, packet_extreme 20 21 21 K95Catalog.path10
      K95Catalog.packet10 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path11, packet_extreme 22 23 22 K95Catalog.path11
      K95Catalog.packet11 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path11, packet_extreme 22 23 23 K95Catalog.path11
      K95Catalog.packet11 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path12, packet_extreme 24 25 24 K95Catalog.path12
      K95Catalog.packet12 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path12, packet_extreme 24 25 25 K95Catalog.path12
      K95Catalog.packet12 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path13, packet_extreme 26 27 26 K95Catalog.path13
      K95Catalog.packet13 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path13, packet_extreme 26 27 27 K95Catalog.path13
      K95Catalog.packet13 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path14, packet_extreme 28 29 28 K95Catalog.path14
      K95Catalog.packet14 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path14, packet_extreme 28 29 29 K95Catalog.path14
      K95Catalog.packet14 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path15, packet_extreme 30 31 30 K95Catalog.path15
      K95Catalog.packet15 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path15, packet_extreme 30 31 31 K95Catalog.path15
      K95Catalog.packet15 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path16, packet_extreme 32 33 32 K95Catalog.path16
      K95Catalog.packet16 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path16, packet_extreme 32 33 33 K95Catalog.path16
      K95Catalog.packet16 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path17, packet_extreme 34 35 34 K95Catalog.path17
      K95Catalog.packet17 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path17, packet_extreme 34 35 35 K95Catalog.path17
      K95Catalog.packet17 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path18, packet_extreme 36 37 36 K95Catalog.path18
      K95Catalog.packet18 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path18, packet_extreme 36 37 37 K95Catalog.path18
      K95Catalog.packet18 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path19, packet_extreme 38 39 38 K95Catalog.path19
      K95Catalog.packet19 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path19, packet_extreme 38 39 39 K95Catalog.path19
      K95Catalog.packet19 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path20, packet_extreme 40 41 40 K95Catalog.path20
      K95Catalog.packet20 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path20, packet_extreme 40 41 41 K95Catalog.path20
      K95Catalog.packet20 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path21, packet_extreme 42 43 42 K95Catalog.path21
      K95Catalog.packet21 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path21, packet_extreme 42 43 43 K95Catalog.path21
      K95Catalog.packet21 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path22, packet_extreme 44 45 44 K95Catalog.path22
      K95Catalog.packet22 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path22, packet_extreme 44 45 45 K95Catalog.path22
      K95Catalog.packet22 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path23, packet_extreme 46 47 46 K95Catalog.path23
      K95Catalog.packet23 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path23, packet_extreme 46 47 47 K95Catalog.path23
      K95Catalog.packet23 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path24, packet_extreme 48 49 48 K95Catalog.path24
      K95Catalog.packet24 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path24, packet_extreme 48 49 49 K95Catalog.path24
      K95Catalog.packet24 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path25, packet_extreme 50 51 50 K95Catalog.path25
      K95Catalog.packet25 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path25, packet_extreme 50 51 51 K95Catalog.path25
      K95Catalog.packet25 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path26, packet_extreme 52 53 52 K95Catalog.path26
      K95Catalog.packet26 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path26, packet_extreme 52 53 53 K95Catalog.path26
      K95Catalog.packet26 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path27, packet_extreme 54 55 54 K95Catalog.path27
      K95Catalog.packet27 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path27, packet_extreme 54 55 55 K95Catalog.path27
      K95Catalog.packet27 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path28, packet_extreme 56 57 56 K95Catalog.path28
      K95Catalog.packet28 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path28, packet_extreme 56 57 57 K95Catalog.path28
      K95Catalog.packet28 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path29, packet_extreme 58 59 58 K95Catalog.path29
      K95Catalog.packet29 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path29, packet_extreme 58 59 59 K95Catalog.path29
      K95Catalog.packet29 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path30, packet_extreme 60 61 60 K95Catalog.path30
      K95Catalog.packet30 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path30, packet_extreme 60 61 61 K95Catalog.path30
      K95Catalog.packet30 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path31, packet_extreme 62 63 62 K95Catalog.path31
      K95Catalog.packet31 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path31, packet_extreme 62 63 63 K95Catalog.path31
      K95Catalog.packet31 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path32, packet_extreme 64 65 64 K95Catalog.path32
      K95Catalog.packet32 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path32, packet_extreme 64 65 65 K95Catalog.path32
      K95Catalog.packet32 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path33, packet_extreme 66 67 66 K95Catalog.path33
      K95Catalog.packet33 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path33, packet_extreme 66 67 67 K95Catalog.path33
      K95Catalog.packet33 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path34, packet_extreme 68 69 68 K95Catalog.path34
      K95Catalog.packet34 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path34, packet_extreme 68 69 69 K95Catalog.path34
      K95Catalog.packet34 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path35, packet_extreme 70 71 70 K95Catalog.path35
      K95Catalog.packet35 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path35, packet_extreme 70 71 71 K95Catalog.path35
      K95Catalog.packet35 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path36, packet_extreme 72 73 72 K95Catalog.path36
      K95Catalog.packet36 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path36, packet_extreme 72 73 73 K95Catalog.path36
      K95Catalog.packet36 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path37, packet_extreme 74 75 74 K95Catalog.path37
      K95Catalog.packet37 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path37, packet_extreme 74 75 75 K95Catalog.path37
      K95Catalog.packet37 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path38, packet_extreme 76 77 76 K95Catalog.path38
      K95Catalog.packet38 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path38, packet_extreme 76 77 77 K95Catalog.path38
      K95Catalog.packet38 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path39, packet_extreme 78 77 78 K95Catalog.path39
      K95Catalog.packet39 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path40, packet_extreme 80 79 79 K95Catalog.path40
      K95Catalog.packet40 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path40, packet_extreme 80 79 80 K95Catalog.path40
      K95Catalog.packet40 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path41, packet_extreme 82 81 81 K95Catalog.path41
      K95Catalog.packet41 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path41, packet_extreme 82 81 82 K95Catalog.path41
      K95Catalog.packet41 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path42, packet_extreme 84 83 83 K95Catalog.path42
      K95Catalog.packet42 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path42, packet_extreme 84 83 84 K95Catalog.path42
      K95Catalog.packet42 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path43, packet_extreme 86 85 85 K95Catalog.path43
      K95Catalog.packet43 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path43, packet_extreme 86 85 86 K95Catalog.path43
      K95Catalog.packet43 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path44, packet_extreme 86 87 87 K95Catalog.path44
      K95Catalog.packet44 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path45, packet_extreme 88 87 88 K95Catalog.path45
      K95Catalog.packet45 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path46, packet_extreme 88 89 89 K95Catalog.path46
      K95Catalog.packet46 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path47, packet_extreme 90 89 90 K95Catalog.path47
      K95Catalog.packet47 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path48, packet_extreme 90 91 91 K95Catalog.path48
      K95Catalog.packet48 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path49, packet_extreme 92 91 92 K95Catalog.path49
      K95Catalog.packet49 (Or.inl rfl)⟩
  · subst d
    exact ⟨K95Catalog.path50, packet_extreme 94 93 93 K95Catalog.path50
      K95Catalog.packet50 (Or.inr rfl)⟩
  · subst d
    exact ⟨K95Catalog.path50, packet_extreme 94 93 94 K95Catalog.path50
      K95Catalog.packet50 (Or.inl rfl)⟩

/-- Every interior target on either of the two actual added 95-edge arms. -/
theorem interior {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hd : 1≤d ∧ d≤94) :
    Q24Rooted.ZeroAt H root Q 46 ⟨95-d,by omega⟩ ∧
    Q24Rooted.ZeroAt H root Q 46 ⟨95+d,by omega⟩ := by
  obtain ⟨w,hw,hx⟩ := catalog_extreme d hd
  exact ⟨Q24Rooted.rooted_left H root g Q 46 d hg hroot w hw (by omega) hx,
    Q24Rooted.rooted_right H root g Q 46 d hg hroot w hw (by omega) hx⟩

end GracefulBoundary.K95Rooted
