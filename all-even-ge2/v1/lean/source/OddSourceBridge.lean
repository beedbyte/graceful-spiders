import OrdinaryPhase
import InteriorComposition
import ShellInduction

namespace GracefulBoundary.EvenBoundary

theorem ordinary_source_shell (t : Nat) (ht : 5≤t) :
    ∃s : List Nat, SourceShell (4*t+1) s := by
  obtain ⟨u,low,high,first,last⟩ :=
    GracefulBoundary.OrdinaryPhase.all_ordinary_source_shells t ht
  refine ⟨u,low.core,first,?_,?_,?_⟩
  · have idx : 2*(4*t+1)-(4*t+4)=4*t+1-3 := by omega
    simpa only [idx] using low.zeroOffset
  · have idx : 2*(4*t+1)-(4*t+3)=4*t+1-2 := by omega
    simpa only [idx] using high.zeroOffset
  · rw [List.getLast?_eq_getElem?] at last
    have len := low.core.length
    simpa only [len,show 2*(4*t+1)+1-1=2*(4*t+1) by omega] using last

theorem int_mem_side (xs : List Int) (x : Int) (hx : x∈xs) :
    x∈GracefulSignedCap.highs xs ∨ x∈GracefulSignedCap.lows xs := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | htail
    · left
      simp [GracefulSignedCap.highs_cons]
    · rcases ih htail with hi | lo
      · right
        simpa [GracefulSignedCap.lows_cons] using hi
      · left
        rw [GracefulSignedCap.highs_cons]
        exact List.mem_cons_of_mem _ lo

theorem int_band_nonneg (n : Nat) (x : Int)
    (hx : x∈GracefulSignedCap.band n) : 0≤x := by
  rcases List.mem_map.mp hx with ⟨y,_,rfl⟩
  simp

theorem shell_entries_nonneg (q : Nat) (s : List Int)
    (hs : GracefulSignedCap.ShellContract q s) :
    ∀x∈s, 0≤x := by
  intro x hx
  rcases int_mem_side s x hx with hi | lo
  · have target := (hs.highSide.mem_iff).mp hi
    rcases List.mem_cons.mp target with rfl | hb
    · simp
      omega
    · exact int_band_nonneg q x hb
  · have target := (hs.lowSide.mem_iff).mp lo
    exact int_band_nonneg q x target

theorem sides_toNat (xs : List Int) :
    GracefulBoundary.highs (xs.map Int.toNat) =
      (GracefulSignedCap.highs xs).map Int.toNat ∧
    GracefulBoundary.lows (xs.map Int.toNat) =
      (GracefulSignedCap.lows xs).map Int.toNat := by
  induction xs with
  | nil => simp [GracefulBoundary.highs,GracefulBoundary.lows,
      GracefulSignedCap.highs,GracefulSignedCap.lows]
  | cons a xs ih =>
    constructor
    · simpa only [List.map_cons,GracefulBoundary.highs_cons,
        GracefulSignedCap.highs_cons] using congrArg (List.cons a.toNat) ih.2
    · simpa only [List.map_cons,GracefulBoundary.lows_cons,
        GracefulSignedCap.lows_cons] using ih.1

theorem edgeSums_toNat (xs : List Int)
    (hn : ∀x∈xs, 0≤x) :
    GracefulBoundary.edgeSums (xs.map Int.toNat) =
      (GracefulSignedCap.edgeSums xs).map Int.toNat := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b ys =>
      have ha : 0≤a := hn a (by simp)
      have hb : 0≤b := hn b (by simp)
      have htail : ∀x∈b::ys,0≤x := by
        intro x hx
        exact hn x (by simp [hx])
      have hsum : (a+b).toNat=a.toNat+b.toNat := by omega
      simp only [List.map_cons,GracefulBoundary.edgeSums,
        GracefulSignedCap.edgeSums]
      rw [hsum]
      exact congrArg (List.cons (a.toNat+b.toNat)) (ih htail)

theorem band_toNat (n : Nat) :
    (GracefulSignedCap.band n).map Int.toNat = List.range n := by
  have f : (Int.toNat ∘ Int.ofNat)=id := by funext x; rfl
  simp [GracefulSignedCap.band,List.map_map,f]

theorem shell_to_source_nat (q : Nat) (s : List Int)
    (hs : GracefulSignedCap.ShellContract q s) :
    SourceShell q (s.map Int.toNat) := by
  have hn := shell_entries_nonneg q s hs
  obtain ⟨phi,plo⟩ := sides_toNat s
  have high := hs.highSide.map Int.toNat
  have low := hs.lowSide.map Int.toNat
  have sums := hs.sums.map Int.toNat
  rw [←phi] at high
  simp only [List.map_cons,band_toNat] at high
  rw [←plo,band_toNat] at low
  rw [←edgeSums_toNat s hn,band_toNat] at sums
  have order : ((q+1)::List.range q).Perm (List.range q++[q+1]) := by
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.count_cons,List.count_append,List.count_nil]
    omega
  have root : (s.map Int.toNat).head?=some (q+1) := by
    simpa using congrArg (Option.map Int.toNat) hs.root
  have firstHigh : (s.map Int.toNat)[1]?=some (q-2) := by
    simpa using congrArg (Option.map Int.toNat) hs.firstHigh
  have zeroEarly : (s.map Int.toNat)[q-3]?=some 0 := by
    simpa using congrArg (Option.map Int.toNat) hs.zeros.1
  have zeroLate : (s.map Int.toNat)[q-2]?=some 0 := by
    simpa using congrArg (Option.map Int.toNat) hs.zeros.2
  have terminal : (s.map Int.toNat)[2*q]?=some 1 := by
    simpa using congrArg (Option.map Int.toNat) hs.terminal
  exact ⟨⟨by simpa using hs.length,high.trans order,low,sums,root⟩,
    firstHigh,zeroEarly,zeroLate,terminal⟩

theorem companion_source_shell (t : Nat) (ht : 5≤t) :
    ∃s : List Nat, SourceShell (4*t+3) s := by
  obtain ⟨cap,_,hc⟩ := GracefulSignedCap.companion_contract_exists t ht
  exact ⟨(GracefulSignedCap.companionSource t cap).map Int.toNat,
    shell_to_source_nat (4*t+3) _ hc⟩

theorem all_odd_source_shells : OddSourceFamily := by
  intro q hq hodd
  have residue : q%4=1 ∨ q%4=3 := by omega
  rcases residue with h1 | h3
  · have ht : 5≤q/4 := by omega
    have eq : 4*(q/4)+1=q := by omega
    simpa only [eq] using ordinary_source_shell (q/4) ht
  · have ht : 5≤q/4 := by omega
    have eq : 4*(q/4)+3=q := by omega
    simpa only [eq] using companion_source_shell (q/4) ht

theorem promoted_packets_from_graft (R : Nat)
    (hgraft : CanonicalGraftLaw) : PromotedPackets R :=
  promoted_packets_of_sources R all_odd_source_shells hgraft

theorem all_interior_from_graft (R D n m : Nat)
    (hR : 18≤R) (hn : 2≤n) (hD : R≤D)
    (hprefix : ∀(a : Fin n) (d : Nat), 2≤d → d<2*R → d≤D →
      NamedDepthZero R n m d a)
    (hlower : ∀(a : Fin n) (d : Nat), 2≤d → d<2*R →
      2*R-d≤22 → NamedDepthZero R n m d a)
    (hgraft : CanonicalGraftLaw) :
    ∀(a : Fin n) (d : Nat), 2≤d → d<2*R →
      NamedDepthZero R n m d a :=
  all_interior_from_source_shells R D n m hR hn hD hprefix hlower
    all_odd_source_shells hgraft

end GracefulBoundary.EvenBoundary
