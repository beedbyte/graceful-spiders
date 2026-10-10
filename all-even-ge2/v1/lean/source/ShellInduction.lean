import ValleyInduction

/-! Additive shell glue for the universally certified companion valley. -/
namespace GracefulSignedCap

theorem parity_map (f : Int → Int) (xs : List Int) :
    highs (xs.map f)=(highs xs).map f ∧
    lows (xs.map f)=(lows xs).map f := by
  induction xs with
  | nil => simp [highs,lows]
  | cons a xs ih =>
    simp [highs_cons,lows_cons,ih.1,ih.2]

def shiftedTail (t : Nat) (cap : List Int) : List Int :=
  (cap.drop 1).map (fun x => x+Int.ofNat (3*t+5))

theorem source_parts (t : Nat) (cap : List Int) :
    companionSource t cap =
      Int.ofNat (4*t+4)::(shiftedTail t cap ++ valley t) := by
  rfl

theorem shifted_band (a h : Nat) :
    (band h).map (fun x => x+Int.ofNat a) =
      (List.range' a h).map Int.ofNat := by
  simp [band,List.range'_eq_map_range,List.map_map]
  intro x hx
  omega

theorem cap_tail_parts (h : Nat) (cap : List Int) (hc : Cap h cap) :
    ∃ tail, cap=Int.ofNat (h+1)::tail ∧
      tail.head?=some (Int.ofNat (h-2)) ∧
      tail.getLast?=some (-2) ∧
      tail.length=2*h+2 ∧
      (highs tail).Perm ((-1)::band h) ∧
      (lows tail).Perm ((-2)::band h) := by
  obtain ⟨xs,eq⟩ := cap_prefix h cap hc
  refine ⟨Int.ofNat (h-2)::xs,eq,by simp,?_,by simpa [eq] using hc.length,?_,?_⟩
  · have old := hc.terminal
    rw [eq] at old
    have ht : (Int.ofNat (h-2)::xs).length=2*h+2 := by
      simpa [eq] using hc.length
    have idx : 2*h+2=1+(Int.ofNat (h-2)::xs).length-1 := by omega
    have : (Int.ofNat (h-2)::xs)[2*h+1]?=some (-2) := by
      simpa using old
    rw [List.getLast?_eq_getElem?, ht]
    simpa using this
  · simpa [eq,lows_cons] using hc.lowSide
  · have old := hc.highSide
    rw [eq,highs_cons] at old
    exact List.Perm.cons_inv old

theorem band_split (m n : Nat) :
    band (m+n)=band m ++ (band n).map (fun x => x+Int.ofNat m) := by
  simp [band,List.range_add,List.map_append,List.map_map]
  intro x hx
  omega

theorem band_succ1 (m : Nat) :
    band (m+1)=band m ++ [Int.ofNat m] := by
  simp [band,List.range_succ]

theorem band_join_one (m n : Nat) :
    ((Int.ofNat m :: (band n).map (fun x => x+Int.ofNat (m+1))) ++ band m).Perm
      (band (m+1+n)) := by
  rw [band_split,band_succ1]
  apply List.perm_iff_count.mpr
  intro x
  simp [List.count_append,List.count_cons]
  omega

theorem band_join_two (m n : Nat) :
    ((Int.ofNat m :: (band n).map (fun x => x+Int.ofNat (m+2))) ++
       (band m ++ [Int.ofNat (m+1)])).Perm (band (m+2+n)) := by
  rw [band_split,band_succ2]
  apply List.perm_iff_count.mpr
  intro x
  simp [List.count_append,List.count_cons]
  omega

theorem source_parities (t : Nat) (cap : List Int)
    (hc : Cap (t-2) cap) :
    lows (companionSource t cap) =
      highs (shiftedTail t cap) ++ highs (valley t) ∧
    highs (companionSource t cap) =
      Int.ofNat (4*t+4)::
        (lows (shiftedTail t cap) ++ lows (valley t)) := by
  have even : (shiftedTail t cap).length%2=0 := by
    simp [shiftedTail,hc.length]
  rw [source_parts]
  obtain ⟨hh,hl⟩ := (append_parity (shiftedTail t cap) (valley t)).1 even
  simp [lows_cons,highs_cons,hh,hl]

theorem shifted_tail_sides (t : Nat) (_ht : 5≤t) (cap : List Int)
    (hc : Cap (t-2) cap) :
    (highs (shiftedTail t cap)).Perm
      (Int.ofNat (3*t+4)::(band (t-2)).map (fun x => x+Int.ofNat (3*t+5))) ∧
    (lows (shiftedTail t cap)).Perm
      (Int.ofNat (3*t+3)::(band (t-2)).map (fun x => x+Int.ofNat (3*t+5))) := by
  obtain ⟨tail,eq,_,_,_,hs,ls⟩ := cap_tail_parts (t-2) cap hc
  have shift : shiftedTail t cap=tail.map (fun x => x+Int.ofNat (3*t+5)) := by
    simp [shiftedTail,eq]
  rw [shift]
  obtain ⟨ph,pl⟩ := parity_map (fun x => x+Int.ofNat (3*t+5)) tail
  rw [ph,pl]
  constructor
  · have mapped := hs.map (fun x => x+Int.ofNat (3*t+5))
    have arith : (-1:Int)+Int.ofNat (3*t+5)=Int.ofNat (3*t+4) := by
      have eq : 3*t+5=(3*t+4)+1 := by omega
      rw [eq]
      simp
      omega
    simpa only [List.map_cons,arith] using mapped
  · have mapped := ls.map (fun x => x+Int.ofNat (3*t+5))
    have arith : (-2:Int)+Int.ofNat (3*t+5)=Int.ofNat (3*t+3) := by
      have eq : 3*t+5=(3*t+3)+2 := by omega
      rw [eq]
      simp
      omega
    simpa only [List.map_cons,arith] using mapped

theorem companion_side_inventories (t : Nat) (ht : 5≤t) (cap : List Int)
    (hc : Cap (t-2) cap) :
    (lows (companionSource t cap)).Perm (band (4*t+3)) ∧
    (highs (companionSource t cap)).Perm
      (Int.ofNat (4*t+4)::band (4*t+3)) := by
  obtain ⟨lo,hi⟩ := source_parities t cap hc
  obtain ⟨sh,sl⟩ := shifted_tail_sides t ht cap hc
  have vc := valley_contract_all t ht
  have eqLow : 3*t+4+1+(t-2)=4*t+3 := by omega
  have eqHigh : 3*t+3+2+(t-2)=4*t+3 := by omega
  constructor
  · rw [lo]
    have combined := sh.append vc.lowSide
    have join := band_join_one (3*t+4) (t-2)
    simpa only [show (3*t+4)+1=3*t+5 by omega,eqLow] using combined.trans join
  · rw [hi]
    apply List.Perm.cons
    have combined := sl.append vc.highSide
    have join := band_join_two (3*t+3) (t-2)
    simpa only [show (3*t+3)+2=3*t+5 by omega,
      show (3*t+3)+1=3*t+4 by omega,eqHigh] using combined.trans join

theorem cap_tail_sums (h : Nat) (hh : 3≤h) (cap : List Int)
    (hc : Cap h cap) :
    (edgeSums (cap.drop 1)).Perm ((-2)::(-1)::band (2*h-1)) := by
  obtain ⟨xs,eq⟩ := cap_prefix h cap hc
  have rootSum : Int.ofNat (h+1)+Int.ofNat (h-2)=Int.ofNat (2*h-1) := by
    have natEq : (h+1)+(h-2)=2*h-1 := by omega
    rw [← natEq]
    simp
  apply List.perm_iff_count.mpr
  intro x
  have old := hc.sums.count_eq x
  rw [eq] at old ⊢
  simp only [edgeSums,rootSum,List.count_cons] at old
  have bandEnd : 2*h=(2*h-1)+1 := by omega
  have bandDecomp : band (2*h)=band (2*h-1) ++ [Int.ofNat (2*h-1)] := by
    calc
      band (2*h)=band ((2*h-1)+1) := by rw [← bandEnd]
      _ = _ := band_succ1 _
  rw [bandDecomp] at old
  simp only [List.count_append,List.count_cons] at old
  simp only [List.count_nil,Nat.zero_add] at old
  change List.count x (edgeSums (Int.ofNat (h-2)::xs)) = _
  simp only [List.count_cons]
  omega

theorem edgeSums_shift (a : Int) (xs : List Int) :
    edgeSums (xs.map (fun x => x+a)) =
      (edgeSums xs).map (fun x => x+2*a) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simp only [List.map_cons,edgeSums]
      have tail : edgeSums ((y+a)::ys.map (fun x => x+a)) =
          (edgeSums (y::ys)).map (fun x => x+2*a) := by
        simpa only [List.map_cons] using ih
      rw [tail]
      congr 1
      omega

theorem shifted_tail_endpoints (t : Nat) (ht : 5≤t) (cap : List Int)
    (hc : Cap (t-2) cap) :
    (shiftedTail t cap).head?=some (Int.ofNat (4*t+1)) ∧
    (shiftedTail t cap).getLast?=some (Int.ofNat (3*t+3)) := by
  obtain ⟨tail,eq,head,last,_,_,_⟩ := cap_tail_parts (t-2) cap hc
  have shift : shiftedTail t cap=tail.map (fun x => x+Int.ofNat (3*t+5)) := by
    simp [shiftedTail,eq]
  rw [shift]
  constructor
  · simp [head]
    have natEq : (t-2-2)+(3*t+5)=4*t+1 := by omega
    exact_mod_cast natEq
  · simp [last]
    omega

theorem shifted_cap_sum_band (a h : Nat) (ha : 1≤a) (hh : 1≤h) :
    (((-2:Int)::(-1)::band (2*h-1)).map
        (fun x => x+2*Int.ofNat a)).Perm
      ((band (2*h+1)).map (fun x => x+Int.ofNat (2*a-2))) := by
  have size : 2*h+1=2+(2*h-1) := by omega
  have offs : 2*a-2+2=2*a := by omega
  rw [size,band_split]
  simp only [List.map_append,List.map_cons,List.map_map]
  have offsI : Int.ofNat (2*a-2)+2=2*Int.ofNat a := by
    have castEq := congrArg Int.ofNat offs
    simpa using castEq
  have first : (-2:Int)+2*Int.ofNat a=Int.ofNat (2*a-2) := by omega
  have second : (-1:Int)+2*Int.ofNat a=Int.ofNat (2*a-2)+1 := by omega
  have tailEq :
      List.map ((fun x => x+Int.ofNat (2*a-2)) ∘
        fun x => x+Int.ofNat 2) (band (2*h-1)) =
      List.map (fun x => x+2*Int.ofNat a) (band (2*h-1)) := by
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply]
    change x+2+Int.ofNat (2*a-2)=x+2*Int.ofNat a
    omega
  have two : band 2=[0,1] := by decide
  rw [two,tailEq]
  simp only [List.map_cons,List.map_nil,List.nil_append,List.cons_append]
  rw [first,second]
  simp [Int.add_comm]

theorem shifted_tail_sums (t : Nat) (ht : 5≤t) (cap : List Int)
    (hc : Cap (t-2) cap) :
    (edgeSums (shiftedTail t cap)).Perm
      ((band (2*t-3)).map (fun x => x+Int.ofNat (6*t+8))) := by
  have hpos : 3≤t-2 := by omega
  have cs := cap_tail_sums (t-2) hpos cap hc
  have mapped := cs.map (fun x => x+2*Int.ofNat (3*t+5))
  have join := shifted_cap_sum_band (3*t+5) (t-2) (by omega) (by omega)
  have eqSize : 2*(t-2)+1=2*t-3 := by omega
  have eqShift : 2*(3*t+5)-2=6*t+8 := by omega
  have combo := mapped.trans join
  simpa only [shiftedTail,edgeSums_shift,eqSize,eqShift] using combo

theorem shell_sum_band_join (m n : Nat) :
    (Int.ofNat (m+4+n)::
      ((band n).map (fun x => x+Int.ofNat (m+4)) ++
        [Int.ofNat m] ++
        (band m ++ [Int.ofNat (m+1),Int.ofNat (m+2),Int.ofNat (m+3)]))).Perm
      (band (m+4+n+1)) := by
  have target : band (m+4+n+1)=
      ((band m ++ [Int.ofNat m,Int.ofNat (m+1),Int.ofNat (m+2),Int.ofNat (m+3)]) ++
        (band n).map (fun x => x+Int.ofNat (m+4))) ++ [Int.ofNat (m+4+n)] := by
    rw [band_succ1,band_split,band_succ4]
  rw [target]
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append,List.count_cons,List.count_nil]
  omega

theorem source_sum_parts (t : Nat) (ht : 5≤t) (cap : List Int)
    (hc : Cap (t-2) cap) :
    edgeSums (companionSource t cap) =
      Int.ofNat (8*t+5)::
        (edgeSums (shiftedTail t cap) ++ [Int.ofNat (6*t+4)] ++
          edgeSums (valley t)) := by
  obtain ⟨first,last⟩ := shifted_tail_endpoints t ht cap hc
  have vfirst := (valley_contract_all t ht).first
  have joined := sums_join (shiftedTail t cap) (valley t)
    (Int.ofNat (3*t+3)) (Int.ofNat (3*t+1)) last vfirst
  obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp first
  rw [source_parts,eq]
  simp only [List.cons_append,edgeSums]
  have joined' : edgeSums (Int.ofNat (4*t+1)::(tail++valley t)) =
      edgeSums (shiftedTail t cap) ++
        [Int.ofNat (3*t+3)+Int.ofNat (3*t+1)] ++ edgeSums (valley t) := by
    simpa only [eq,List.cons_append] using joined
  rw [joined']
  have rootSum : Int.ofNat (4*t+4)+Int.ofNat (4*t+1)=Int.ofNat (8*t+5) := by
    have natEq : (4*t+4)+(4*t+1)=8*t+5 := by omega
    simpa using congrArg Int.ofNat natEq
  have seam : Int.ofNat (3*t+3)+Int.ofNat (3*t+1)=Int.ofNat (6*t+4) := by
    have natEq : (3*t+3)+(3*t+1)=6*t+4 := by omega
    simpa using congrArg Int.ofNat natEq
  rw [rootSum,seam]
  simp only [eq]

theorem companion_sum_inventory (t : Nat) (ht : 5≤t) (cap : List Int)
    (hc : Cap (t-2) cap) :
    (edgeSums (companionSource t cap)).Perm (band (2*(4*t+3))) := by
  rw [source_sum_parts t ht cap hc]
  have shifted := shifted_tail_sums t ht cap hc
  have valleySums := (valley_contract_all t ht).sums
  have raw := shell_sum_band_join (6*t+4) (2*t-3)
  have eq1 : (6*t+4)+4=6*t+8 := by omega
  have eq2 : (6*t+4)+4+(2*t-3)=8*t+5 := by omega
  have eq3 : (6*t+4)+4+(2*t-3)+1=2*(4*t+3) := by omega
  have eqTotal : 8*t+5+1=2*(4*t+3) := by omega
  have eq4 : (6*t+4)+1=6*t+5 := by omega
  have eq5 : (6*t+4)+2=6*t+6 := by omega
  have eq6 : (6*t+4)+3=6*t+7 := by omega
  have joined :
      (Int.ofNat (8*t+5)::
        ((band (2*t-3)).map (fun x => x+Int.ofNat (6*t+8)) ++
          [Int.ofNat (6*t+4)] ++
          (band (6*t+4) ++
            [Int.ofNat (6*t+5),Int.ofNat (6*t+6),Int.ofNat (6*t+7)]))).Perm
        (band (2*(4*t+3))) := by
    simpa only [eq1,eq2,eqTotal,eq4,eq5,eq6] using raw
  apply List.perm_iff_count.mpr
  intro x
  have shc := shifted.count_eq x
  have vcc := valleySums.count_eq x
  have jc := joined.count_eq x
  simp only [List.count_cons,List.count_append,List.count_nil,Nat.zero_add] at shc vcc jc ⊢
  omega

theorem companion_firstHigh (t : Nat) (ht : 5≤t) (cap : List Int)
    (hc : Cap (t-2) cap) :
    (companionSource t cap)[1]?=some (Int.ofNat (4*t+1)) := by
  obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp
    (shifted_tail_endpoints t ht cap hc).1
  rw [source_parts,eq]
  simp

theorem companion_terminal (t : Nat) (ht : 5≤t) (cap : List Int)
    (hc : Cap (t-2) cap) :
    (companionSource t cap)[2*(4*t+3)]?=some 1 := by
  let front : List Int := Int.ofNat (4*t+4)::shiftedTail t cap
  have frontlen : front.length=2*t-1 := by
    simp [front,shiftedTail,hc.length]
    omega
  have source : companionSource t cap=front++valley t := by
    simp [source_parts,front,List.cons_append]
  rw [source]
  rw [List.getElem?_append_right (by rw [frontlen]; omega)]
  have idx : 2*(4*t+3)-front.length=6*t+7 := by rw [frontlen]; omega
  rw [idx]
  exact (valley_contract_all t ht).terminal

theorem companion_contract_all (t : Nat) (ht : 5≤t) (cap : List Int)
    (hc : Cap (t-2) cap) :
    ShellContract (4*t+3) (companionSource t cap) := by
  have sides := companion_side_inventories t ht cap hc
  have zeroes := companion_zeros t ht cap hc
  have idx1 : 4*t+3-2=4*t+1 := by omega
  have idx0 : 4*t+3-3=4*t := by omega
  refine ⟨companion_length t ht cap hc,?_,?_,companion_terminal t ht cap hc,
    sides.1,sides.2,companion_sum_inventory t ht cap hc,?_⟩
  · simp [companionSource]
    omega
  · rw [idx1]
    exact companion_firstHigh t ht cap hc
  · rw [idx0,idx1]
    exact zeroes

theorem companion_contract_exists (t : Nat) (ht : 5≤t) :
    ∃cap, Cap (t-2) cap ∧
      ShellContract (4*t+3) (companionSource t cap) := by
  obtain ⟨cap,hc⟩ := exists_cap (t-2) (by omega)
  exact ⟨cap,hc,companion_contract_all t ht cap hc⟩

end GracefulSignedCap
