import FullRotatable
namespace GracefulBoundary.TailGraft
open EvenBoundary.Flexible

/-- Already shifted retained prefix, including its actual boundary join to q-2.
The interface is supplied explicitly; canonical all-r prefix existence is not assumed. -/
structure RetainedPrefix (r q : Nat) (p : List Nat) : Prop where
  length : p.length=2*r-3
  low : (highs p).Perm (List.range' q (r-2)++[r+q-2+1])
  high : (lows p).Perm (List.range' q (r-2))
  sumsWithJoin : (edgeSums (p++[q-2])).Perm (List.range' (2*q-1) (2*r-3))
  first : p.head?=some (r+q-2+1)

theorem side_partition (r q : Nat) (hr : 4≤r) :
    (List.range' q (r-2)++List.range q).Perm (List.range (r+q-2)) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,count_band,List.count_range]
  repeat (any_goals split)
  all_goals omega

theorem sum_partition (r q : Nat) (hr : 4≤r) (hq : 2≤q) :
    (List.range' (2*q-1) (2*r-3)++List.range (2*q-1)).Perm (List.range (2*(r+q-2))) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,count_band,List.count_range]
  repeat (any_goals split)
  all_goals omega

/-- Complete structural tail graft from explicit retained-prefix and first-high interfaces. -/
theorem supplied_tail_graft (r q : Nat) (hr : 4≤r) (hq : 2≤q) (p u : List Nat)
    (hp : RetainedPrefix r q p) (hu : CorePacket q ((q+1)::(q-2)::u)) :
    CorePacket (r+q-2) (p++(q-2)::u) := by
  have odd : ¬p.length%2=0 := by rw [hp.length]; omega
  have utlow : (lows ((q-2)::u)).Perm (List.range q) := by
    apply List.perm_iff_count.mpr
    intro x
    have eq := hu.low.count_eq x
    simp only [highs_cons,List.count_cons,List.count_append,List.count_nil] at eq
    omega
  have uthigh : (highs ((q-2)::u)).Perm (List.range q) := by simpa only [lows_cons] using hu.high
  have utsums : (edgeSums ((q-2)::u)).Perm (List.range (2*q-1)) := by
    apply List.perm_iff_count.mpr
    intro x
    have eq := hu.sums.count_eq x
    have root : q+1+(q-2)=2*q-1 := by omega
    simp only [edgeSums,root,List.count_cons,List.count_range,Nat.beq_eq_true_eq] at eq ⊢
    repeat (any_goals (first | omega | split at eq | split))
  refine ⟨?_,?_,?_,?_,?_⟩
  · have len := hu.length
    simp only [List.length_cons] at len
    simp only [List.length_append,List.length_cons,hp.length]
    omega
  · rw [highs_append,ite_eq_right odd]
    have perm := hp.low.append utlow
    apply perm.trans
    apply List.perm_iff_count.mpr
    intro x
    have eq := (side_partition r q hr).count_eq x
    simp only [List.count_append,List.count_cons,List.count_nil] at eq ⊢
    omega
  · rw [lows_append,ite_eq_right odd]
    exact (hp.high.append uthigh).trans (side_partition r q hr)
  · rw [edgeSums_overlap]
    exact (hp.sumsWithJoin.append utsums).trans (sum_partition r q hr hq)
  · obtain ⟨t,eq⟩ := List.head?_eq_some_iff.mp hp.first
    rw [eq]; rfl

theorem graft_target_lookup (r q deficit : Nat) (hr : 4≤r) (p u : List Nat)
    (hp : p.length=2*r-3) (hd : 1≤2*q-deficit)
    (target : ((q+1)::u)[2*q-deficit]?=some 0) :
    (p++u)[2*(r+q-2)-deficit]?=some 0 := by
  have index : 2*(r+q-2)-deficit=p.length+(2*q-deficit-1) := by omega
  rw [index,List.getElem?_append_right (by omega)]
  have oldindex : 2*q-deficit=(2*q-deficit-1)+1 := by omega
  rw [oldindex,List.getElem?_cons_succ] at target
  simpa using target

end GracefulBoundary.TailGraft
