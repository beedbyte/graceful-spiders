import Deficit24Seeds
import CoreSeamAdapter
namespace GracefulBoundary.LowBand
open EvenBoundary EvenBoundary.Flexible

/-- Supplied first-high source, lifted to every target radius at least q+2. -/
theorem promote (q R d : Nat) (hq : 2≤q) (hR : q+2≤R) (u : List Nat)
    (hd : ExtremePacket q d ((q+1)::(q-2)::u)) : ∃c,ExtremePacket R d c := by
  obtain ⟨p,hp⟩ := retained_prefix_exists (R-q+2) q (by omega) hq
  have next := Scattered.supplied_extreme_graft (R-q+2) q d (by omega) hq p u hp hd
  have size : R-q+2+q-2=R := by omega
  exact ⟨_,by simpa only [size] using next⟩

end GracefulBoundary.LowBand
