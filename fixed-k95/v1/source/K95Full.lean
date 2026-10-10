import K95Catalog8
import K95Tip
namespace GracefulBoundary.K95Full

def DepthZero (n m d : Nat) (a : Fin n) : Prop :=
  ∃ h : d-1<95, ∃ f : SpiderVertex n m 95 → Nat,
    Graceful (spiderGraph n m 95) (95*n+m) f ∧ f (.arm a ⟨d-1,h⟩)=0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem interior (n m d : Nat) (hn : 2≤n) (a : Fin n)
    (hd : 1≤d ∧ d≤94) : DepthZero n m d a := by
  have hsplit : d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=5 ∨ d=6 ∨ d=7 ∨ d=8 ∨ d=9 ∨ d=10 ∨ d=11 ∨ d=12 ∨ d=13 ∨ d=14 ∨ d=15 ∨ d=16 ∨ d=17 ∨ d=18 ∨ d=19 ∨ d=20 ∨ d=21 ∨ d=22 ∨ d=23 ∨ d=24 ∨ d=25 ∨ d=26 ∨ d=27 ∨ d=28 ∨ d=29 ∨ d=30 ∨ d=31 ∨ d=32 ∨ d=33 ∨ d=34 ∨ d=35 ∨ d=36 ∨ d=37 ∨ d=38 ∨ d=39 ∨ d=40 ∨ d=41 ∨ d=42 ∨ d=43 ∨ d=44 ∨ d=45 ∨ d=46 ∨ d=47 ∨ d=48 ∨ d=49 ∨ d=50 ∨ d=51 ∨ d=52 ∨ d=53 ∨ d=54 ∨ d=55 ∨ d=56 ∨ d=57 ∨ d=58 ∨ d=59 ∨ d=60 ∨ d=61 ∨ d=62 ∨ d=63 ∨ d=64 ∨ d=65 ∨ d=66 ∨ d=67 ∨ d=68 ∨ d=69 ∨ d=70 ∨ d=71 ∨ d=72 ∨ d=73 ∨ d=74 ∨ d=75 ∨ d=76 ∨ d=77 ∨ d=78 ∨ d=79 ∨ d=80 ∨ d=81 ∨ d=82 ∨ d=83 ∨ d=84 ∨ d=85 ∨ d=86 ∨ d=87 ∨ d=88 ∨ d=89 ∨ d=90 ∨ d=91 ∨ d=92 ∨ d=93 ∨ d=94 := by omega
  rcases hsplit with h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60|h61|h62|h63|h64|h65|h66|h67|h68|h69|h70|h71|h72|h73|h74|h75|h76|h77|h78|h79|h80|h81|h82|h83|h84|h85|h86|h87|h88|h89|h90|h91|h92|h93|h94
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 2 1 n m K95Catalog.path0 K95Catalog.packet0 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 2 3 n m K95Catalog.path1 K95Catalog.packet1 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 2 3 n m K95Catalog.path1 K95Catalog.packet1 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 4 5 n m K95Catalog.path2 K95Catalog.packet2 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 4 5 n m K95Catalog.path2 K95Catalog.packet2 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 6 7 n m K95Catalog.path3 K95Catalog.packet3 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 6 7 n m K95Catalog.path3 K95Catalog.packet3 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 8 9 n m K95Catalog.path4 K95Catalog.packet4 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 8 9 n m K95Catalog.path4 K95Catalog.packet4 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 10 11 n m K95Catalog.path5 K95Catalog.packet5 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 10 11 n m K95Catalog.path5 K95Catalog.packet5 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 12 13 n m K95Catalog.path6 K95Catalog.packet6 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 12 13 n m K95Catalog.path6 K95Catalog.packet6 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 14 15 n m K95Catalog.path7 K95Catalog.packet7 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 14 15 n m K95Catalog.path7 K95Catalog.packet7 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 16 17 n m K95Catalog.path8 K95Catalog.packet8 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 16 17 n m K95Catalog.path8 K95Catalog.packet8 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 18 19 n m K95Catalog.path9 K95Catalog.packet9 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 18 19 n m K95Catalog.path9 K95Catalog.packet9 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 20 21 n m K95Catalog.path10 K95Catalog.packet10 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 20 21 n m K95Catalog.path10 K95Catalog.packet10 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 22 23 n m K95Catalog.path11 K95Catalog.packet11 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 22 23 n m K95Catalog.path11 K95Catalog.packet11 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 24 25 n m K95Catalog.path12 K95Catalog.packet12 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 24 25 n m K95Catalog.path12 K95Catalog.packet12 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 26 27 n m K95Catalog.path13 K95Catalog.packet13 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 26 27 n m K95Catalog.path13 K95Catalog.packet13 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 28 29 n m K95Catalog.path14 K95Catalog.packet14 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 28 29 n m K95Catalog.path14 K95Catalog.packet14 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 30 31 n m K95Catalog.path15 K95Catalog.packet15 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 30 31 n m K95Catalog.path15 K95Catalog.packet15 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 32 33 n m K95Catalog.path16 K95Catalog.packet16 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 32 33 n m K95Catalog.path16 K95Catalog.packet16 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 34 35 n m K95Catalog.path17 K95Catalog.packet17 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 34 35 n m K95Catalog.path17 K95Catalog.packet17 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 36 37 n m K95Catalog.path18 K95Catalog.packet18 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 36 37 n m K95Catalog.path18 K95Catalog.packet18 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 38 39 n m K95Catalog.path19 K95Catalog.packet19 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 38 39 n m K95Catalog.path19 K95Catalog.packet19 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 40 41 n m K95Catalog.path20 K95Catalog.packet20 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 40 41 n m K95Catalog.path20 K95Catalog.packet20 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 42 43 n m K95Catalog.path21 K95Catalog.packet21 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 42 43 n m K95Catalog.path21 K95Catalog.packet21 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 44 45 n m K95Catalog.path22 K95Catalog.packet22 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 44 45 n m K95Catalog.path22 K95Catalog.packet22 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 46 47 n m K95Catalog.path23 K95Catalog.packet23 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 46 47 n m K95Catalog.path23 K95Catalog.packet23 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 48 49 n m K95Catalog.path24 K95Catalog.packet24 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 48 49 n m K95Catalog.path24 K95Catalog.packet24 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 50 51 n m K95Catalog.path25 K95Catalog.packet25 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 50 51 n m K95Catalog.path25 K95Catalog.packet25 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 52 53 n m K95Catalog.path26 K95Catalog.packet26 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 52 53 n m K95Catalog.path26 K95Catalog.packet26 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 54 55 n m K95Catalog.path27 K95Catalog.packet27 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 54 55 n m K95Catalog.path27 K95Catalog.packet27 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 56 57 n m K95Catalog.path28 K95Catalog.packet28 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 56 57 n m K95Catalog.path28 K95Catalog.packet28 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 58 59 n m K95Catalog.path29 K95Catalog.packet29 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 58 59 n m K95Catalog.path29 K95Catalog.packet29 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 60 61 n m K95Catalog.path30 K95Catalog.packet30 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 60 61 n m K95Catalog.path30 K95Catalog.packet30 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 62 63 n m K95Catalog.path31 K95Catalog.packet31 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 62 63 n m K95Catalog.path31 K95Catalog.packet31 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 64 65 n m K95Catalog.path32 K95Catalog.packet32 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 64 65 n m K95Catalog.path32 K95Catalog.packet32 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 66 67 n m K95Catalog.path33 K95Catalog.packet33 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 66 67 n m K95Catalog.path33 K95Catalog.packet33 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 68 69 n m K95Catalog.path34 K95Catalog.packet34 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 68 69 n m K95Catalog.path34 K95Catalog.packet34 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 70 71 n m K95Catalog.path35 K95Catalog.packet35 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 70 71 n m K95Catalog.path35 K95Catalog.packet35 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 72 73 n m K95Catalog.path36 K95Catalog.packet36 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 72 73 n m K95Catalog.path36 K95Catalog.packet36 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 74 75 n m K95Catalog.path37 K95Catalog.packet37 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 74 75 n m K95Catalog.path37 K95Catalog.packet37 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 76 77 n m K95Catalog.path38 K95Catalog.packet38 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 76 77 n m K95Catalog.path38 K95Catalog.packet38 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 78 77 n m K95Catalog.path39 K95Catalog.packet39 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 80 79 n m K95Catalog.path40 K95Catalog.packet40 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 80 79 n m K95Catalog.path40 K95Catalog.packet40 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 82 81 n m K95Catalog.path41 K95Catalog.packet41 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 82 81 n m K95Catalog.path41 K95Catalog.packet41 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 84 83 n m K95Catalog.path42 K95Catalog.packet42 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 84 83 n m K95Catalog.path42 K95Catalog.packet42 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 86 85 n m K95Catalog.path43 K95Catalog.packet43 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 86 85 n m K95Catalog.path43 K95Catalog.packet43 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 86 87 n m K95Catalog.path44 K95Catalog.packet44 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 88 87 n m K95Catalog.path45 K95Catalog.packet45 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 88 89 n m K95Catalog.path46 K95Catalog.packet46 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 90 89 n m K95Catalog.path47 K95Catalog.packet47 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 90 91 n m K95Catalog.path48 K95Catalog.packet48 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 92 91 n m K95Catalog.path49 K95Catalog.packet49 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 94 93 n m K95Catalog.path50 K95Catalog.packet50 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 46 94 93 n m K95Catalog.path50 K95Catalog.packet50 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩

theorem arm_depth_zero (n m : Nat) (hn : 2≤n) (a : Fin n) (d : Fin 95) :
    ∃ f : SpiderVertex n m 95 → Nat,
      Graceful (spiderGraph n m 95) (95*n+m) f ∧ f (.arm a d)=0 := by
  have hd := d.isLt
  by_cases hi : d.val+1≤94
  · obtain ⟨hlt,f,hf,hz⟩ := interior n m (d.val+1) hn a ⟨by omega,hi⟩
    have he : (⟨d.val+1-1,hlt⟩ : Fin 95)=d := by
      apply Fin.ext
      change d.val+1-1=d.val
      omega
    exact ⟨f,hf,by simpa only [he] using hz⟩
  · have he : d=⟨94,by decide⟩ := by
      apply Fin.ext
      change d.val=94
      omega
    rw [he]
    simpa [Nat.mul_comm] using (K95Tip.tips_prescribed_zero n m (by omega) a).1

/-- Every actual named vertex of S(95^n,1^m), with a separate labeling per target. -/
theorem all_vertices (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 95) :
    ∃ f : SpiderVertex n m 95 → Nat,
      Graceful (spiderGraph n m 95) (95*n+m) f ∧ f v=0 := by
  cases v with
  | center => exact K95Boundary.center_zero n m
  | leaf a => exact K95Boundary.leaf_zero n m a
  | arm a d => exact arm_depth_zero n m hn a d

theorem unique_zero (n m : Nat) (hn : 2≤n) (v : SpiderVertex n m 95) :
    ∃ f : SpiderVertex n m 95 → Nat,
      Graceful (spiderGraph n m 95) (95*n+m) f ∧
      ∀ w, f w=0 ↔ w=v := by
  obtain ⟨f,hf,hz⟩ := all_vertices n m hn v
  refine ⟨f,hf,?_⟩
  intro w
  constructor
  · intro hw
    exact hf.vertices.injective w v (hw.trans hz.symm)
  · intro hw
    simpa [hw] using hz

end GracefulBoundary.K95Full
#print GracefulBoundary.K95Full.all_vertices
#print axioms GracefulBoundary.K95Full.all_vertices
#print axioms GracefulBoundary.K95Full.unique_zero
