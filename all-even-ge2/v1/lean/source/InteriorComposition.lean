import UniversalSeam
import GenericShellTransfer

namespace GracefulBoundary.EvenBoundary

open GracefulUniversalSeam
open Flexible

/-- Zero at one named arm vertex of the actual spider. -/
def NamedDepthZero (R n m d : Nat) (a : Fin n) : Prop :=
  ∃ (hlt : d-1 < 2*R) (f : SpiderVertex n m (2*R) → Nat),
    Graceful (spiderGraph n m (2*R)) (n*(2*R)+m) f ∧
    f (.arm a ⟨d-1,hlt⟩) = 0

/-- The missing general graft obligation is explicit: every admissible
    source radius and either conserved deficit must yield a target packet. -/
def PromotedPackets (R : Nat) : Prop :=
  ∀ q deficit : Nat, 21 ≤ q → q % 2 = 1 →
    (deficit = q+2 ∨ deficit = q+3) → 5 ≤ R-q+2 →
    ∃ c : List Nat, ExtremePacket R deficit c

/-- Exactly the source information used by the mathematical canonical graft.
    `CorePacket` is the frozen balanced shell inventory and sum contract. -/
structure SourceShell (q : Nat) (s : List Nat) : Prop where
  core : CorePacket q s
  firstHigh : s[1]? = some (q-2)
  zeroEarly : s[q-3]? = some 0
  zeroLate : s[q-2]? = some 0
  terminal : s[2*q]? = some 1

/-- The unproved source-family obligation, kept as a theorem premise. -/
def OddSourceFamily : Prop :=
  ∀ q : Nat, 21 ≤ q → q % 2 = 1 → ∃ s : List Nat, SourceShell q s

/-- The unproved generic graft obligation. The same promoted target shell
    must certify both conserved deficits on the actual target radius. -/
def CanonicalGraftLaw : Prop :=
  ∀ (q R : Nat) (s : List Nat), 21 ≤ q → q % 2 = 1 →
    SourceShell q s → q+2 ≤ R →
    ∃ c : List Nat, ExtremePacket R (q+2) c ∧ ExtremePacket R (q+3) c

theorem promoted_packets_of_sources (R : Nat)
    (hfamily : OddSourceFamily) (hgraft : CanonicalGraftLaw) :
    PromotedPackets R := by
  intro q deficit hq hodd hdef hradius
  obtain ⟨s,hs⟩ := hfamily q hq hodd
  obtain ⟨c,hc2,hc3⟩ := hgraft q R s hq hodd hs (by omega)
  rcases hdef with h2 | h3
  · exact ⟨c,by simpa only [h2] using hc2⟩
  · exact ⟨c,by simpa only [h3] using hc3⟩

/-- Conditional interior composition. The prefix and low-deficit branches
    are explicit graph theorems, while the source branch uses the concrete
    named-graph packet transfer proved in GenericShellTransfer. -/
theorem all_interior_named_depths (R D n m : Nat)
    (hR : 18 ≤ R) (hn : 2 ≤ n) (hD : R ≤ D)
    (hprefix : ∀ (a : Fin n) (d : Nat), 2 ≤ d → d < 2*R → d ≤ D →
      NamedDepthZero R n m d a)
    (hlower : ∀ (a : Fin n) (d : Nat), 2 ≤ d → d < 2*R →
      2*R-d ≤ 22 → NamedDepthZero R n m d a)
    (hpackets : PromotedPackets R) :
    ∀ (a : Fin n) (d : Nat), 2 ≤ d → d < 2*R →
      NamedDepthZero R n m d a := by
  intro a d hd0 hd1
  rcases arithmetic_seam R D d hD hd0 hd1 with hp | hl | hs
  · exact hprefix a d hd0 hd1 hp
  · exact hlower a d hd0 hd1 hl
  · obtain ⟨q,hq,hodd,hdef,hradius⟩ := hs
    obtain ⟨c,hc⟩ := hpackets q (2*R-d) hq hodd hdef hradius
    obtain ⟨hlt,f,hf,hzero⟩ :=
      named_arm_zero_from_packet R n m (2*R-d) (by omega) hn a c hc
    have hdepth : 2*R-(2*R-d)-1 = d-1 := by omega
    subst_vars
    exact ⟨by omega,f,hf,by simpa only [hdepth] using hzero⟩

/-- The final conditional bridge explicitly names the proposed source family
    and canonical graft law. It covers interior long-arm vertices only. -/
theorem all_interior_from_source_shells (R D n m : Nat)
    (hR : 18 ≤ R) (hn : 2 ≤ n) (hD : R ≤ D)
    (hprefix : ∀ (a : Fin n) (d : Nat), 2 ≤ d → d < 2*R → d ≤ D →
      NamedDepthZero R n m d a)
    (hlower : ∀ (a : Fin n) (d : Nat), 2 ≤ d → d < 2*R →
      2*R-d ≤ 22 → NamedDepthZero R n m d a)
    (hfamily : OddSourceFamily) (hgraft : CanonicalGraftLaw) :
    ∀ (a : Fin n) (d : Nat), 2 ≤ d → d < 2*R →
      NamedDepthZero R n m d a :=
  all_interior_named_depths R D n m hR hn hD hprefix hlower
    (promoted_packets_of_sources R hfamily hgraft)

end GracefulBoundary.EvenBoundary

#print axioms GracefulBoundary.EvenBoundary.all_interior_named_depths
#print axioms GracefulBoundary.EvenBoundary.promoted_packets_of_sources
#print axioms GracefulBoundary.EvenBoundary.all_interior_from_source_shells
