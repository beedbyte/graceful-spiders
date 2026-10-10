import ScatteredData
namespace GracefulBoundary.Scattered
open EvenBoundary.Flexible LabelOne

theorem decode_append (N : Nat) (high : Bool) (p u : List Nat) :
    decode N high (p++u)=decode N high p++decode N (if p.length%2=0 then high else !high) u := by
  induction p generalizing high with
  | nil => simp [decode]
  | cons a p ih =>
    by_cases even : p.length%2=0
    · have odd : ¬(p.length+1)%2=0 := by omega
      cases high <;> simp [decode,ih,even,odd]
    · have next : (p.length+1)%2=0 := by omega
      cases high <;> simp [decode,ih,even,next]

theorem decode_zero_lookup (N i : Nat) (high : Bool) (c : List Nat) (hz : c[i]?=some 0) :
    (decode N high c)[i]?=some (if i%2=0 then if high then N else 0 else if high then 0 else N) := by
  induction c generalizing i high with
  | nil => simp at hz
  | cons a c ih =>
    cases i with
    | zero =>
      have eq : a=0 := by simpa using hz
      subst a; cases high <;> rfl
    | succ i =>
      have old : c[i]?=some 0 := by simpa using hz
      rw [decode,List.getElem?_cons_succ,ih i (!high) old]
      by_cases even : i%2=0
      · have next : ¬(i+1)%2=0 := by omega
        cases high <;> simp [even,next]
      · have next : (i+1)%2=0 := by omega
        cases high <;> simp [even,next]

theorem supplied_extreme_graft (r q deficit : Nat) (hr : 4≤r) (hq : 2≤q) (p u : List Nat)
    (hp : TailGraft.RetainedPrefix r q p) (hu : ExtremePacket q deficit ((q+1)::(q-2)::u)) :
    ExtremePacket (r+q-2) deficit (p++(q-2)::u) := by
  have depth := hu.depthPositive
  have index : 2*(r+q-2)-deficit=p.length+(2*q-deficit-1) := by rw [hp.length]; omega
  refine ⟨TailGraft.supplied_tail_graft r q hr hq p u hp hu.core,by omega,?_,?_⟩
  · exact TailGraft.graft_target_lookup r q deficit hr p ((q-2)::u) hp.length depth hu.zeroOffset
  · intro N
    have old := hu.decodedExtreme N
    change ((q+1)::decode N true ((q-2)::u))[2*q-deficit]?=some (extremeValue N deficit) at old
    have oldindex : 2*q-deficit=(2*q-deficit-1)+1 := by omega
    rw [oldindex,List.getElem?_cons_succ] at old
    have odd : ¬p.length%2=0 := by rw [hp.length]; omega
    rw [decode_append,ite_eq_right odd,index,List.getElem?_append_right (by rw [decode_length]; omega)]
    simpa only [decode_length,Nat.add_sub_cancel_left,Bool.not_false] using old

end GracefulBoundary.Scattered
