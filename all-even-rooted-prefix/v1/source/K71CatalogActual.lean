import K71Catalog4
import Q54Actual
namespace GracefulBoundary.K71Catalog

theorem low_actual (n m d : Nat) (hn : 2≤n) (a : Fin n)
    (hd : 1≤d ∧ d≤57) : Q54.DepthZero n m d a := by
  have hsplit : d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=5 ∨ d=6 ∨ d=7 ∨ d=8 ∨ d=9 ∨ d=10 ∨ d=11 ∨ d=12 ∨ d=13 ∨ d=14 ∨ d=15 ∨ d=16 ∨ d=17 ∨ d=18 ∨ d=19 ∨ d=20 ∨ d=21 ∨ d=22 ∨ d=23 ∨ d=24 ∨ d=25 ∨ d=26 ∨ d=27 ∨ d=28 ∨ d=29 ∨ d=30 ∨ d=31 ∨ d=32 ∨ d=33 ∨ d=34 ∨ d=35 ∨ d=36 ∨ d=37 ∨ d=38 ∨ d=39 ∨ d=40 ∨ d=41 ∨ d=42 ∨ d=43 ∨ d=44 ∨ d=45 ∨ d=46 ∨ d=47 ∨ d=48 ∨ d=49 ∨ d=50 ∨ d=51 ∨ d=52 ∨ d=53 ∨ d=54 ∨ d=55 ∨ d=56 ∨ d=57 := by omega
  rcases hsplit with h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 2 1 n m path1 packet1 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 2 3 n m path2 packet2 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 2 3 n m path2 packet2 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 4 5 n m path4 packet4 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 4 5 n m path4 packet4 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 6 7 n m path6 packet6 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 6 7 n m path6 packet6 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 8 9 n m path8 packet8 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 8 9 n m path8 packet8 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 10 11 n m path10 packet10 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 10 11 n m path10 packet10 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 12 13 n m path12 packet12 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 12 13 n m path12 packet12 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 14 15 n m path14 packet14 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 14 15 n m path14 packet14 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 16 17 n m path16 packet16 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 16 17 n m path16 packet16 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 18 19 n m path18 packet18 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 18 19 n m path18 packet18 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 20 21 n m path20 packet20 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 20 21 n m path20 packet20 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 22 23 n m path22 packet22 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 22 23 n m path22 packet22 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 24 25 n m path24 packet24 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 24 25 n m path24 packet24 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 26 27 n m path26 packet26 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 26 27 n m path26 packet26 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 28 29 n m path28 packet28 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 28 29 n m path28 packet28 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 30 31 n m path30 packet30 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 30 31 n m path30 packet30 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 32 33 n m path32 packet32 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 32 33 n m path32 packet32 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 34 35 n m path34 packet34 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 34 35 n m path34 packet34 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 36 37 n m path36 packet36 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 36 37 n m path36 packet36 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 38 39 n m path38 packet38 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 38 39 n m path38 packet38 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 40 41 n m path40 packet40 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 40 41 n m path40 packet40 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 42 43 n m path42 packet42 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 42 43 n m path42 packet42 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 44 45 n m path44 packet44 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 44 45 n m path44 packet44 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 46 47 n m path46 packet46 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 46 47 n m path46 packet46 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 48 49 n m path48 packet48 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 48 49 n m path48 packet48 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 50 51 n m path50 packet50 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 50 51 n m path50 packet50 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 52 53 n m path52 packet52 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 52 53 n m path52 packet52 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 54 55 n m path54 packet54 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 54 55 n m path54 packet54 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 56 57 n m path56 packet56 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 56 57 n m path56 packet56 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩

theorem tail_actual (n m d : Nat) (hn : 2≤n) (a : Fin n)
    (hd : d=69 ∨ d=70) : Q54.DepthZero n m d a := by
  rcases hd with h|h
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 70 69 n m path70 packet70 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 70 69 n m path70 packet70 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩

end GracefulBoundary.K71Catalog
