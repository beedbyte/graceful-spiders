import CenterBoundary
namespace GracefulBoundary.FullFixed.RootZeroTip
open LabelOne

structure CorePacket (r : Nat) (c : List Nat) : Prop where
  length : c.length=2*r+1
  low : (highs c).Perm (List.range r++[r])
  high : (lows c).Perm (List.range r)
  sums : (edgeSums c).Perm (List.range (2*r))
  first : c.head?=some r

def armLabels (Q r : Nat) (c : List Nat) : List Nat := (decode (Q+2*r) false c).tail

theorem decoded_first (Q r : Nat) (c : List Nat) (hc : CorePacket r c) :
    decode (Q+2*r) false c=r::armLabels Q r c := by
  obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp hc.first
  simp [eq,decode,armLabels]

theorem arm_permutation (Q r : Nat) (c : List Nat) (hc : CorePacket r c) :
    (armLabels Q r c).Perm (List.range r++List.range' (Q+r+1) r) := by
  have whole := (decode_side_permutations (Q+2*r) c).2.trans
    (hc.low.append ((hc.high.map (fun x => Q+2*r-x)).trans (reverse_range_band Q r)))
  rw [decoded_first Q r c hc] at whole
  apply List.perm_iff_count.mpr
  intro x
  have ht := whole.count_eq x
  simp only [List.count_cons,List.count_append,List.count_nil] at ht ⊢
  omega

theorem arm_length (Q r : Nat) (c : List Nat) (hc : CorePacket r c) : (armLabels Q r c).length=2*r := by
  simp [armLabels,List.length_tail,decode_length,hc.length]

theorem arm_differences (Q r : Nat) (c : List Nat) (hc : CorePacket r c) :
    (edgeDiffs (decode (Q+2*r) false c)).Perm (List.range' (Q+1) (2*r)) := by
  have hb : ∀ s∈edgeSums c,s≤Q+2*r := by
    intro s hs
    have mem := hc.sums.mem_iff.mp hs
    simp only [List.mem_range] at mem
    omega
  rw [decode_sums (Q+2*r) c false hb]
  have he : (List.range' (Q+1) (2*r)).reverse=(List.range (2*r)).map (fun x => Q+2*r-x) := by
    rw [List.reverse_range']
    by_cases zero : r=0
    · subst r; rfl
    · rw [show Q+1+2*r-1=Q+2*r by omega]
  have perm := hc.sums.map (fun x => Q+2*r-x)
  rw [←he] at perm
  exact perm.trans (List.reverse_perm _)


end GracefulBoundary.FullFixed.RootZeroTip
