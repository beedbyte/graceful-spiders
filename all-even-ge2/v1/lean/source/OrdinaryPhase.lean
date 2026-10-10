import ValleyInventories
namespace GracefulBoundary.OrdinaryPhase
open EvenBoundary.Flexible

def capWord (a : Nat) (c : List Nat) : List Nat := c.tail.map (fun x => a+x)
def P (t : Nat) (c : List Nat) : List Nat := (4*t+2)::(capWord (3*t+3) c++valley t)

theorem cap_word_facts (b a : Nat) (c : List Nat) (hb : 3≤b) (hc : Cap b c) :
    (capWord a c).length=2*b ∧
    (highs (capWord a c)).Perm (List.range' a b) ∧
    (lows (capWord a c)).Perm (List.range' a b) ∧
    (edgeSums (capWord a c)).Perm (List.range' (2*a) (2*b-1)) ∧
    (capWord a c).head?=some (a+(b-2)) ∧ (capWord a c).getLast?=some (a+1) := by
  obtain ⟨u,shape⟩ := List.head?_eq_some_iff.mp hc.core.first
  have len : u.length=2*b := by have h:=hc.core.length; rw [shape] at h; simp only [List.length_cons] at h; omega
  have ne : u≠[] := by intro h; rw [h] at len; simp at len; omega
  have first : u.head?=some (b-2) := by
    have h:=hc.firstHigh
    simpa only [shape,List.getElem?_cons_succ,←List.head?_eq_getElem?] using h
  have last : u.getLast?=some 1 := by
    have h:=hc.last
    simpa only [shape,List.getLast?_cons_of_ne_nil ne] using h
  have hi : (highs u).Perm (List.range b) := by simpa only [shape,lows_cons] using hc.core.high
  have lo : (lows u).Perm (List.range b) := by
    apply List.perm_iff_count.mpr; intro x
    have h:=hc.core.low.count_eq x
    simp only [shape,highs_cons,List.count_cons,List.count_append,List.count_nil] at h
    omega
  have root : edgeSums c=(2*b-1)::edgeSums u := by
    obtain ⟨v,eq⟩ := List.head?_eq_some_iff.mp first
    rw [shape,eq]
    simp only [edgeSums]
    congr 1; omega
  have sums : (edgeSums u).Perm (List.range (2*b-1)) := by
    apply List.perm_iff_count.mpr; intro x
    have h:=hc.core.sums.count_eq x
    simp only [root,List.count_cons,List.count_range,Nat.beq_eq_true_eq] at h ⊢
    repeat (any_goals (first | omega | split at h | split))
  refine ⟨by simpa only [capWord,shape,List.tail_cons,List.length_map] using len,?_,?_,?_,?_,?_⟩
  · have h:=hi.map (fun x => a+x)
    rw [←List.range'_eq_map_range] at h
    simpa only [capWord,shape,List.tail_cons,highs_map] using h
  · have h:=lo.map (fun x => a+x)
    rw [←List.range'_eq_map_range] at h
    simpa only [capWord,shape,List.tail_cons,lows_map] using h
  · have h:=sums.map (fun x => 2*a+x)
    rw [←List.range'_eq_map_range] at h
    simpa only [capWord,shape,List.tail_cons,FixedDepth.edgeSums_add] using h
  · simp only [capWord,shape,List.tail_cons,List.head?_map,first,Option.map_some]
  · simp only [capWord,shape,List.tail_cons,List.getLast?_map,last,Option.map_some]

theorem side_join (t : Nat) (ht : 5≤t) :
    (List.range' (3*t+3) (t-2)++List.range (3*t+3)).Perm (List.range (4*t+1)) := by
  apply List.perm_iff_count.mpr; intro x
  simp only [List.count_append,count_band,List.count_range]
  repeat (any_goals split)
  all_goals omega

theorem sum_join (t : Nat) (ht : 5≤t) :
    ((8*t+1)::(List.range' (6*t+6) (2*(t-2)-1)++(6*t+5)::List.range (6*t+5))).Perm
      (List.range (2*(4*t+1))) := by
  apply List.perm_iff_count.mpr; intro x
  simp only [List.count_append,List.count_cons,count_band,List.count_range,Nat.beq_eq_true_eq]
  repeat (any_goals split)
  all_goals omega

/-- Complete source shell for every t>=5 and ANY ordinary cap, by symbolic interval inventories. -/
theorem P_core (t : Nat) (c : List Nat) (ht : 5≤t) (hc : Cap (t-2) c) :
    CorePacket (4*t+1) (P t c) := by
  obtain ⟨len,hi,lo,sums,first,last⟩ := cap_word_facts (t-2) (3*t+3) c (by omega) hc
  have even : (capWord (3*t+3) c).length%2=0 := by rw [len]; omega
  refine ⟨?_,?_,?_,?_,rfl⟩
  · simp only [P,List.length_cons,List.length_append,len,valley_length]; omega
  · rw [P,highs_cons,lows_append,ite_eq_left even]
    have h:=((lo.append (valley_sides t).2).trans (side_join t ht)).count_eq
    apply List.perm_iff_count.mpr; intro x
    have old:=h x
    simp only [show 4*t+1+1=4*t+2 by omega,List.count_cons,List.count_append,List.count_nil] at old ⊢
    omega
  · rw [P,lows_cons,highs_append,ite_eq_left even]
    exact (hi.append (valley_sides t).1).trans (side_join t ht)
  · have root : edgeSums (P t c)=(8*t+1)::edgeSums (capWord (3*t+3) c++valley t) := by
      obtain ⟨u,shape⟩ := List.head?_eq_some_iff.mp first
      rw [P,shape]
      simp only [List.cons_append,edgeSums]
      congr 1; omega
    have join : 3*t+3+1+(3*t+1)=6*t+5 := by omega
    have start : 2*(3*t+3)=6*t+6 := by omega
    rw [start] at sums
    rw [root,FixedDepth.edgeSums_append_known _ _ _ _ last (valley_first t),join]
    exact ((sums.append ((valley_sums t).cons (6*t+5))).cons (8*t+1)).trans (sum_join t ht)

theorem P_first_high (t : Nat) (c : List Nat) (ht : 5≤t) (hc : Cap (t-2) c) :
    (P t c)[1]?=some ((4*t+1)-2) := by
  have first := (cap_word_facts (t-2) (3*t+3) c (by omega) hc).2.2.2.2.1
  have value : 3*t+3+(t-2-2)=4*t+1-2 := by omega
  rw [P,List.getElem?_cons_succ,←List.head?_eq_getElem?,List.head?_append,first,value]
  rfl

theorem P_last (t : Nat) (c : List Nat) : (P t c).getLast?=some 1 := by
  rw [P,List.getLast?_cons,List.getLast?_append,valley_last]; rfl

theorem pre_zero (t : Nat) : (pre t)[2*t+1]?=some 0 := by
  have h:=pre_last t
  rw [List.getLast?_eq_getElem?,pre_length,show 2*t+2-1=2*t+1 by omega] at h
  exact h

theorem valley_low_zero (t : Nat) : (valley t)[2*t+1]?=some 0 := by
  simp only [valley,List.append_assoc]
  rw [List.getElem?_append_left (by rw [pre_length]; omega)]
  exact pre_zero t

theorem valley_high_zero (t : Nat) : (valley t)[2*t+2]?=some 0 := by
  simp only [valley,List.append_assoc]
  rw [List.getElem?_append_right (by rw [pre_length]; omega),
    show 2*t+2-(pre t).length=0 by rw [pre_length]; omega]
  rw [←List.head?_eq_getElem?,List.head?_append,up_first]
  rfl

theorem P_lookup (t i : Nat) (c : List Nat) :
    (P t c)[1+(capWord (3*t+3) c).length+i]?=(valley t)[i]? := by
  have eq : 1+(capWord (3*t+3) c).length+i=(capWord (3*t+3) c).length+i+1 := by omega
  rw [eq,P,List.getElem?_cons_succ,List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem P_low_zero (t : Nat) (c : List Nat) (ht : 5≤t) (hc : Cap (t-2) c) :
    (P t c)[4*t+1-3]?=some 0 := by
  have len := (cap_word_facts (t-2) (3*t+3) c (by omega) hc).1
  have eq : 4*t+1-3=1+(capWord (3*t+3) c).length+(2*t+1) := by rw [len]; omega
  rw [eq,P_lookup]; exact valley_low_zero t

theorem P_high_zero (t : Nat) (c : List Nat) (ht : 5≤t) (hc : Cap (t-2) c) :
    (P t c)[4*t+1-2]?=some 0 := by
  have len := (cap_word_facts (t-2) (3*t+3) c (by omega) hc).1
  have eq : 4*t+1-2=1+(capWord (3*t+3) c).length+(2*t+2) := by rw [len]; omega
  rw [eq,P_lookup]; exact valley_high_zero t

theorem P_low_extreme (t : Nat) (c : List Nat) (ht : 5≤t) (hc : Cap (t-2) c) :
    ExtremePacket (4*t+1) (4*t+4) (P t c) := by
  have index : 2*(4*t+1)-(4*t+4)=4*t+1-3 := by omega
  refine ⟨P_core t c ht hc,by omega,by rw [index]; exact P_low_zero t c ht hc,?_⟩
  intro N
  have h := Scattered.decode_zero_lookup N (4*t+1-3) false (P t c) (P_low_zero t c ht hc)
  simpa only [index,show (4*t+1-3)%2=0 by omega,ite_true,Bool.false_eq_true,ite_false,
    extremeValue,show (4*t+4)%2=0 by omega] using h

theorem P_high_extreme (t : Nat) (c : List Nat) (ht : 5≤t) (hc : Cap (t-2) c) :
    ExtremePacket (4*t+1) (4*t+3) (P t c) := by
  have index : 2*(4*t+1)-(4*t+3)=4*t+1-2 := by omega
  refine ⟨P_core t c ht hc,by omega,by rw [index]; exact P_high_zero t c ht hc,?_⟩
  intro N
  have h := Scattered.decode_zero_lookup N (4*t+1-2) false (P t c) (P_high_zero t c ht hc)
  simpa only [index,show ¬(4*t+1-2)%2=0 by omega,ite_false,Bool.false_eq_true,
    extremeValue,show ¬(4*t+3)%2=0 by omega] using h

/-- Unconditional existence of the two-deficit ordinary source phase at every t>=5. -/
theorem all_ordinary_source_shells (t : Nat) (ht : 5≤t) :
    ∃u,ExtremePacket (4*t+1) (4*t+4) u ∧ ExtremePacket (4*t+1) (4*t+3) u ∧
      u[1]?=some (4*t+1-2) ∧ u.getLast?=some 1 := by
  obtain ⟨c,hc⟩ := caps (t-2) (by omega)
  exact ⟨P t c,P_low_extreme t c ht hc,P_high_extreme t c ht hc,P_first_high t c ht hc,P_last t c⟩

/-- Actual source-radius named spiders; each target uses its own labeling. -/
theorem ordinary_source_actual_spider (t n m : Nat) (ht : 5≤t) (hn : 2≤n) (a : Fin n) :
    (∃f : SpiderVertex n m (2*(4*t+1)) → Nat,
      Graceful (spiderGraph n m (2*(4*t+1))) (n*(2*(4*t+1))+m) f ∧
      f (.arm a ⟨4*t-3,by omega⟩)=0) ∧
    (∃f : SpiderVertex n m (2*(4*t+1)) → Nat,
      Graceful (spiderGraph n m (2*(4*t+1))) (n*(2*(4*t+1))+m) f ∧
      f (.arm a ⟨4*t-2,by omega⟩)=0) := by
  obtain ⟨u,low,high,_,_⟩ := all_ordinary_source_shells t ht
  constructor
  · obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider (4*t+1) n m (4*t+4) (by omega) hn u low a
    have eq : (⟨2*(4*t+1)-(4*t+4)-1,hlt⟩ : Fin (2*(4*t+1)))=⟨4*t-3,by omega⟩ := Fin.ext (by dsimp only; omega)
    rw [eq] at hz; exact ⟨f,hf,hz⟩
  · obtain ⟨hlt,f,hf,hz⟩ := FullFixed.supplied_extreme_spider (4*t+1) n m (4*t+3) (by omega) hn u high a
    have eq : (⟨2*(4*t+1)-(4*t+3)-1,hlt⟩ : Fin (2*(4*t+1)))=⟨4*t-2,by omega⟩ := Fin.ext (by dsimp only; omega)
    rw [eq] at hz; exact ⟨f,hf,hz⟩

/-- Universal target-radius graft, with the retained-prefix existence premise visible. -/
theorem ordinary_graft_packets (R t : Nat) (ht : 5≤t) (hr : 4*t+3≤R)
    (prefixes : ∃p,TailGraft.RetainedPrefix (R-(4*t+1)+2) (4*t+1) p) :
    ∃u,ExtremePacket R (4*t+4) u ∧ ExtremePacket R (4*t+3) u := by
  obtain ⟨p,hp⟩ := prefixes
  obtain ⟨u,low,high,first,_⟩ := all_ordinary_source_shells t ht
  obtain ⟨v,shape⟩ := List.head?_eq_some_iff.mp low.core.first
  have firstv : v.head?=some (4*t+1-2) := by
    simpa only [shape,List.getElem?_cons_succ,←List.head?_eq_getElem?] using first
  obtain ⟨w,shapev⟩ := List.head?_eq_some_iff.mp firstv
  rw [shape,shapev] at low high
  have hlo := Scattered.supplied_extreme_graft (R-(4*t+1)+2) (4*t+1) (4*t+4) (by omega) (by omega) p w hp low
  have hhi := Scattered.supplied_extreme_graft (R-(4*t+1)+2) (4*t+1) (4*t+3) (by omega) (by omega) p w hp high
  have size : R-(4*t+1)+2+(4*t+1)-2=R := by omega
  rw [size] at hlo hhi
  exact ⟨_,hlo,hhi⟩

theorem ordinary_graft_actual_spider (R t n m : Nat) (ht : 5≤t) (hr : 4*t+3≤R) (hn : 2≤n)
    (prefixes : ∃p,TailGraft.RetainedPrefix (R-(4*t+1)+2) (4*t+1) p) (a : Fin n) :
    (∃ (hlt : 2*R-(4*t+4)-1<2*R) (f : SpiderVertex n m (2*R) → Nat),
      Graceful (spiderGraph n m (2*R)) (n*(2*R)+m) f ∧ f (.arm a ⟨2*R-(4*t+4)-1,hlt⟩)=0) ∧
    (∃ (hlt : 2*R-(4*t+3)-1<2*R) (f : SpiderVertex n m (2*R) → Nat),
      Graceful (spiderGraph n m (2*R)) (n*(2*R)+m) f ∧ f (.arm a ⟨2*R-(4*t+3)-1,hlt⟩)=0) := by
  obtain ⟨u,low,high⟩ := ordinary_graft_packets R t ht hr prefixes
  exact ⟨FullFixed.supplied_extreme_spider R n m (4*t+4) (by omega) hn u low a,
    FullFixed.supplied_extreme_spider R n m (4*t+3) (by omega) hn u high a⟩

end GracefulBoundary.OrdinaryPhase
