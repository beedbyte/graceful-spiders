import GraftSplice
import TailGraftInterface
import OrdinaryPhase

namespace GracefulBoundary.EvenBoundary

open Flexible

/-- The generic source interface forces the two-entry head required by the
existing retained-prefix graft theorem. -/
theorem source_head_pair (q : Nat) (source : List Nat)
    (hs : SourceShell q source) :
    ∃u, source=(q+1)::(q-2)::u := by
  obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp hs.core.first
  have htail : tail.head?=some (q-2) := by
    simpa only [eq,List.getElem?_cons_succ,←List.head?_eq_getElem?] using hs.firstHigh
  obtain ⟨u,eqTail⟩ := List.head?_eq_some_iff.mp htail
  exact ⟨u,by rw [eq,eqTail]⟩

/-- A retained-prefix certificate already gives the full target core for
every source shell. No source-family-specific constructor enters this step. -/
theorem core_of_retained_prefix (R q : Nat) (source cap : List Nat)
    (hq : 21≤q) (hR : q+2≤R)
    (hs : SourceShell q source)
    (hp : TailGraft.RetainedPrefix (R-q+2) q cap) :
    CorePacket R (splice cap source) := by
  obtain ⟨u,shape⟩ := source_head_pair q source hs
  have hr : 4≤R-q+2 := by omega
  have radius : R-q+2+q-2=R := by omega
  have packet := TailGraft.supplied_tail_graft (R-q+2) q hr
    (by omega) cap u hp (by simpa only [shape] using hs.core)
  simpa only [splice,shape,List.tail_cons,radius] using packet

/-- The exact remaining prefix existence statement; this has no hidden
finite radius list or fixed source pattern. -/
def AllRetainedPrefixes : Prop :=
  ∀(q R : Nat), 21≤q → q%2=1 → q+2≤R →
    ∃cap : List Nat, TailGraft.RetainedPrefix (R-q+2) q cap

theorem core_graft_of_retained_prefixes
    (hp : AllRetainedPrefixes) : CanonicalCoreGraftLaw := by
  intro q R source hq hodd hs hR
  obtain ⟨cap,hcap⟩ := hp q R hq hodd hR
  have hlen : cap.length=2*(R-q)+1 := by
    have h := hcap.length
    omega
  exact ⟨cap,hlen,core_of_retained_prefix R q source cap hq hR hs hcap⟩

/-- The exact seam is `2q-1` precisely when the retained prefix ends at
`q+1`. This is the terminal fact needed to turn an internal sum band into
the `RetainedPrefix.sumsWithJoin` field. -/
theorem retained_join_of_terminal (r q : Nat) (cap : List Nat)
    (hr : 4≤r) (hq : 2≤q)
    (hlast : cap.getLast?=some (q+1))
    (hsums : (edgeSums cap).Perm (List.range' (2*q) (2*r-4))) :
    (edgeSums (cap++[q-2])).Perm (List.range' (2*q-1) (2*r-3)) := by
  have join := GracefulBoundary.edgeSums_join cap (q+1) (q-2) [] hlast
  have seam : q+1+(q-2)=2*q-1 := by omega
  have joined : edgeSums (cap++[q-2])=edgeSums cap++[2*q-1] := by
    simpa [GracefulBoundary.edgeSums,seam] using join
  have countEq : 2*r-3=(2*r-4)+1 := by omega
  have startEq : 2*q-1+1=2*q := by omega
  have target : List.range' (2*q-1) (2*r-3) =
      (2*q-1)::List.range' (2*q) (2*r-4) := by
    rw [countEq,List.range'_succ,startEq]
  rw [joined,target]
  apply List.perm_iff_count.mpr
  intro x
  have old := hsums.count_eq x
  simp only [List.count_append,List.count_cons,List.count_nil]
  omega

/-- A convenient independent interface for a recurrence-generated prefix.
The terminal is separate from the internal sum band, so their contribution
to the boundary edge is visible. -/
structure InternalPrefix (r q : Nat) (cap : List Nat) : Prop where
  length : cap.length=2*r-3
  low : (highs cap).Perm (List.range' q (r-2)++[r+q-2+1])
  high : (lows cap).Perm (List.range' q (r-2))
  internalSums : (edgeSums cap).Perm (List.range' (2*q) (2*r-4))
  first : cap.head?=some (r+q-2+1)
  last : cap.getLast?=some (q+1)

theorem retained_of_internal_prefix (r q : Nat) (cap : List Nat)
    (hr : 4≤r) (hq : 2≤q) (hp : InternalPrefix r q cap) :
    TailGraft.RetainedPrefix r q cap :=
  ⟨hp.length,hp.low,hp.high,
    retained_join_of_terminal r q cap hr hq hp.last hp.internalSums,hp.first⟩

/-- The one missing small-radius ordinary cap. -/
def H2 : List Nat := [3,0,0,1,1]

theorem H2_valid : GracefulBoundary.OrdinaryPhase.Cap 2 H2 := by
  refine ⟨?_,by decide,by decide⟩
  constructor <;> decide

theorem caps_from_two (s : Nat) (hs : 2≤s) :
    ∃c,GracefulBoundary.OrdinaryPhase.Cap s c := by
  by_cases h2 : s=2
  · subst s
    exact ⟨H2,H2_valid⟩
  · exact GracefulBoundary.OrdinaryPhase.caps s (by omega)

theorem edgeSums_shift_nat (q : Nat) (xs : List Nat) :
    edgeSums (xs.map (fun x => q+x)) =
      (edgeSums xs).map (fun x => 2*q+x) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b ys =>
      simp only [List.map_cons,edgeSums]
      have tail : edgeSums ((q+b)::ys.map (fun x => q+x)) =
          (edgeSums (b::ys)).map (fun x => 2*q+x) := by
        simpa only [List.map_cons] using ih
      rw [tail]
      congr 1
      omega

theorem shifted_ordinary_cap_prefix (s q : Nat) (c : List Nat)
    (hc : GracefulBoundary.OrdinaryPhase.Cap s c) :
    InternalPrefix (s+2) q (c.map (fun x => q+x)) := by
  have n1 : s+2-2=s := by omega
  have n2 : 2*(s+2)-3=2*s+1 := by omega
  have n3 : 2*(s+2)-4=2*s := by omega
  have n4 : s+2+q-2+1=q+(s+1) := by omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_map,n2] using hc.core.length
  · rw [GracefulBoundary.highs_map]
    have mapped := hc.core.low.map (fun x => q+x)
    simpa only [n1,n4,List.range'_eq_map_range,List.map_append,
      List.map_cons,List.map_nil] using mapped
  · rw [GracefulBoundary.lows_map]
    have mapped := hc.core.high.map (fun x => q+x)
    simpa only [n1,List.range'_eq_map_range] using mapped
  · rw [edgeSums_shift_nat]
    have mapped := hc.core.sums.map (fun x => 2*q+x)
    simpa only [n3,List.range'_eq_map_range] using mapped
  · simpa [List.head?_map,n4] using congrArg (Option.map (fun x => q+x)) hc.core.first
  · simpa using congrArg (Option.map (fun x => q+x)) hc.last

theorem retained_prefix_exists (r q : Nat) (hr : 4≤r) (hq : 2≤q) :
    ∃cap : List Nat, TailGraft.RetainedPrefix r q cap := by
  obtain ⟨c,hc⟩ := caps_from_two (r-2) (by omega)
  have radius : r-2+2=r := by omega
  have intern := shifted_ordinary_cap_prefix (r-2) q c hc
  exact ⟨c.map (fun x => q+x),
    by simpa only [radius] using
      retained_of_internal_prefix (r-2+2) q _ (by omega) hq intern⟩

theorem all_retained_prefixes : AllRetainedPrefixes := by
  intro q R hq hodd hR
  exact retained_prefix_exists (R-q+2) q (by omega) (by omega)

theorem all_canonical_core_grafts : CanonicalCoreGraftLaw :=
  core_graft_of_retained_prefixes all_retained_prefixes

theorem all_canonical_grafts : CanonicalGraftLaw :=
  canonical_graft_of_core_graft all_canonical_core_grafts

end GracefulBoundary.EvenBoundary
