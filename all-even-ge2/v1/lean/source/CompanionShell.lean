import CompanionValley

/-! Exact source interface and one finite calibration; no all-t theorem is asserted. -/
namespace GracefulSignedCap

def companionSource (t : Nat) (cap : List Int) : List Int :=
  [Int.ofNat (4*t+4)] ++ (cap.drop 1).map (fun x => x+Int.ofNat (3*t+5)) ++ valley t

structure ShellContract (q : Nat) (c : List Int) : Prop where
  length : c.length=2*q+1
  root : c.head?=some (Int.ofNat (q+1))
  firstHigh : c[1]?=some (Int.ofNat (q-2))
  terminal : c[2*q]?=some 1
  lowSide : (lows c).Perm (band q)
  highSide : (highs c).Perm (Int.ofNat (q+1)::band q)
  sums : (edgeSums c).Perm (band (2*q))
  zeros : c[q-3]?=some 0 ∧ c[q-2]?=some 0

theorem companion_length (t : Nat) (ht : 5≤t) (cap : List Int)
    (hc : Cap (t-2) cap) :
    (companionSource t cap).length=2*(4*t+3)+1 := by
  simp [companionSource, valley_length, hc.length]
  omega

theorem companion_zeros (t : Nat) (ht : 5≤t) (cap : List Int)
    (hc : Cap (t-2) cap) :
    (companionSource t cap)[4*t]?=some 0 ∧
    (companionSource t cap)[4*t+1]?=some 0 := by
  let front : List Int := [Int.ofNat (4*t+4)] ++
    (cap.drop 1).map (fun x => x+Int.ofNat (3*t+5))
  have frontlen : front.length=2*t-1 := by
    simp [front,hc.length]
    omega
  change (front ++ valley t)[4*t]?=some 0 ∧
    (front ++ valley t)[4*t+1]?=some 0
  obtain ⟨hz1,hz2⟩ := valley_zeros t
  constructor
  · rw [List.getElem?_append_right (by rw [frontlen]; omega)]
    have idx : 4*t-front.length=2*t+1 := by rw [frontlen]; omega
    rw [idx]; exact hz1
  · rw [List.getElem?_append_right (by rw [frontlen]; omega)]
    have idx : 4*t+1-front.length=2*t+2 := by rw [frontlen]; omega
    rw [idx]; exact hz2

theorem companion_skeleton_exists (t : Nat) (ht : 5≤t) :
    ∃cap, Cap (t-2) cap ∧
      (companionSource t cap).length=2*(4*t+3)+1 ∧
      (companionSource t cap)[4*t]?=some 0 ∧
      (companionSource t cap)[4*t+1]?=some 0 := by
  obtain ⟨cap,hc⟩ := exists_cap (t-2) (by omega)
  exact ⟨cap,hc,companion_length t ht cap hc,(companion_zeros t ht cap hc).1,
    (companion_zeros t ht cap hc).2⟩

theorem companion5_valid : ShellContract 23 (companionSource 5 E3) := by
  constructor <;> decide

theorem companion6_valid : ShellContract 27 (companionSource 6 E4) := by
  constructor <;> decide

theorem companion5_exact : companionSource 5 E3 =
    [24,21,21,22,22,19,20,20,18,16,15,13,12,10,9,7,6,4,3,1,0,0,2,3,5,6,8,9,11,12,14,15,17,18,19,17,16,14,13,11,10,8,7,5,4,2,1] := by
  decide

end GracefulSignedCap
