import InteriorComposition
import GraftCoreBridge

namespace GracefulBoundary.EvenBoundary

open Flexible

/-- The accepted even-shell graft appends the source after deleting its root. -/
def splice (cap source : List Nat) : List Nat := cap ++ source.tail

private theorem suffix_zero (cap source : List Nat) (j : Nat)
    (hj : 1 ≤ j) (hz : source[j]? = some 0) :
    (splice cap source)[cap.length+j-1]? = some 0 := by
  cases source with
  | nil => simp at hz
  | cons x tail =>
    obtain ⟨i,rfl⟩ : ∃ i, j=i+1 := ⟨j-1,by omega⟩
    simp only [List.getElem?_cons_succ] at hz
    dsimp only [splice]
    simp only [List.tail_cons]
    have index : cap.length+(i+1)-1=cap.length+i := by omega
    rw [index,List.getElem?_append_right (by omega)]
    simpa using hz

/-- Both source zeros move by exactly twice the radius difference. -/
theorem splice_zeros (R q : Nat) (cap source : List Nat)
    (hq : 5 ≤ q) (hR : q+2 ≤ R)
    (hlen : cap.length = 2*(R-q)+1)
    (hs : SourceShell q source) :
    (splice cap source)[2*R-(q+3)]? = some 0 ∧
    (splice cap source)[2*R-(q+2)]? = some 0 := by
  constructor
  · have hi : 2*R-(q+3)=cap.length+(q-3)-1 := by omega
    rw [hi]
    exact suffix_zero cap source (q-3) (by omega) hs.zeroEarly
  · have hi : 2*R-(q+2)=cap.length+(q-2)-1 := by omega
    rw [hi]
    exact suffix_zero cap source (q-2) (by omega) hs.zeroLate

/-- Exact remaining graft interface: once the list-level CorePacket is
    established, both ExtremePacket obligations follow automatically. -/
theorem target_extremes_of_splice_core (R q : Nat) (cap source : List Nat)
    (hq : 21 ≤ q) (hR : q+2 ≤ R)
    (hlen : cap.length = 2*(R-q)+1)
    (hs : SourceShell q source)
    (hcore : CorePacket R (splice cap source)) :
    ExtremePacket R (q+2) (splice cap source) ∧
    ExtremePacket R (q+3) (splice cap source) := by
  have hz := splice_zeros R q cap source (by omega) hR hlen hs
  constructor
  · exact extreme_of_core_zero R (q+2) _ hcore (by omega) hz.2
  · exact extreme_of_core_zero R (q+3) _ hcore (by omega) hz.1

/-- The sole remaining list-level graft obligation. It states the exact cap
    length and complete target inventory/sum contract, with no zero fields. -/
def CanonicalCoreGraftLaw : Prop :=
  ∀ (q R : Nat) (source : List Nat), 21 ≤ q → q % 2 = 1 →
    SourceShell q source → q+2 ≤ R →
    ∃ cap : List Nat, cap.length = 2*(R-q)+1 ∧
      CorePacket R (splice cap source)

/-- No decoded-extreme, depth, or odd-complement obligation remains once
    the genuine list-level CorePacket graft has been supplied. -/
theorem canonical_graft_of_core_graft
    (hcore : CanonicalCoreGraftLaw) : CanonicalGraftLaw := by
  intro q R source hq hodd hs hR
  obtain ⟨cap,hlen,hpacket⟩ := hcore q R source hq hodd hs hR
  have both := target_extremes_of_splice_core R q cap source hq hR hlen hs hpacket
  exact ⟨splice cap source,both.1,both.2⟩

/-- The already compiled arithmetic and actual-graph bridges now depend on
    exactly one new list-level graft theorem rather than an ExtremePacket law. -/
theorem all_interior_from_core_graft (R D n m : Nat)
    (hR : 18 ≤ R) (hn : 2 ≤ n) (hD : R ≤ D)
    (hprefix : ∀ (a : Fin n) (d : Nat), 2 ≤ d → d < 2*R → d ≤ D →
      NamedDepthZero R n m d a)
    (hlower : ∀ (a : Fin n) (d : Nat), 2 ≤ d → d < 2*R →
      2*R-d ≤ 22 → NamedDepthZero R n m d a)
    (hfamily : OddSourceFamily) (hcore : CanonicalCoreGraftLaw) :
    ∀ (a : Fin n) (d : Nat), 2 ≤ d → d < 2*R →
      NamedDepthZero R n m d a :=
  all_interior_from_source_shells R D n m hR hn hD hprefix hlower hfamily
    (canonical_graft_of_core_graft hcore)

end GracefulBoundary.EvenBoundary

#print axioms GracefulBoundary.EvenBoundary.target_extremes_of_splice_core
#print axioms GracefulBoundary.EvenBoundary.canonical_graft_of_core_graft
#print axioms GracefulBoundary.EvenBoundary.all_interior_from_core_graft
