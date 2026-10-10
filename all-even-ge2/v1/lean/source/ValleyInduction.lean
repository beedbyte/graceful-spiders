import CompanionShell

/-! Additive symbolic work on the universal companion valley inventory. -/
namespace GracefulSignedCap

theorem cons_split (xs : List Int) :
    (∀a, highs (a::xs)=a::lows xs) ∧ (∀a, lows (a::xs)=highs xs) := by
  induction xs with
  | nil => constructor <;> intro a <;> rfl
  | cons b ys ih =>
    constructor
    · intro a; simpa [highs] using congrArg (List.cons a) (ih.2 b).symm
    · intro a; simpa [lows] using (ih.1 b).symm

theorem highs_cons (a : Int) (xs : List Int) : highs (a::xs)=a::lows xs :=
  (cons_split xs).1 a

theorem lows_cons (a : Int) (xs : List Int) : lows (a::xs)=highs xs :=
  (cons_split xs).2 a

theorem append_parity (xs ys : List Int) :
    (xs.length%2=0 →
      highs (xs++ys)=highs xs++highs ys ∧ lows (xs++ys)=lows xs++lows ys) ∧
    (xs.length%2=1 →
      highs (xs++ys)=highs xs++lows ys ∧ lows (xs++ys)=lows xs++highs ys) := by
  induction xs with
  | nil =>
    constructor
    · intro _; simp [highs,lows]
    · intro h; simp at h
  | cons a xs ih =>
    constructor
    · intro he
      have ho : xs.length%2=1 := by simp at he; omega
      obtain ⟨hh,hl⟩ := ih.2 ho
      constructor
      · simp [highs_cons, hl, List.cons_append]
      · simp [lows_cons, hh, List.cons_append]
    · intro ho
      have he : xs.length%2=0 := by simp at ho; omega
      obtain ⟨hh,hl⟩ := ih.1 he
      constructor
      · simp [highs_cons, hl, List.cons_append]
      · simp [lows_cons, hh, List.cons_append]

def LI (t : Nat) : List Int := (L t).map Int.ofNat
def AI (t : Nat) : List Int := (A t).map Int.ofNat
def DI (t : Nat) : List Int := (D t).map Int.ofNat

theorem LI_length (t : Nat) : (LI t).length=2*(t+1) := by simp [LI,L_length]
theorem AI_length (t : Nat) : (AI t).length=2*t := by simp [AI,A_length]
theorem DI_length (t : Nat) : (DI t).length=2*t+1 := by simp [DI,D_length]

theorem LI_step (t : Nat) : LI (t+1) = [Int.ofNat (3*t+4),Int.ofNat (3*t+3)] ++ LI t := by
  simp [LI,L]
  congr 1 <;> omega

theorem AI_step (t : Nat) : AI (t+1) = AI t ++ [Int.ofNat (3*t+2),Int.ofNat (3*t+3)] := by
  simp [AI,A]

theorem DI_step (t : Nat) : DI (t+1) = [Int.ofNat (3*t+4),Int.ofNat (3*t+2)] ++ DI t := by
  simp [DI,D]

theorem LI_high_step (t : Nat) : highs (LI (t+1)) = Int.ofNat (3*t+4)::highs (LI t) := by
  rw [LI_step]; rfl
theorem LI_low_step (t : Nat) : lows (LI (t+1)) = Int.ofNat (3*t+3)::lows (LI t) := by
  rw [LI_step]; rfl

theorem AI_high_step (t : Nat) : highs (AI (t+1)) = highs (AI t) ++ [Int.ofNat (3*t+2)] := by
  rw [AI_step]
  have even : (AI t).length%2=0 := by rw [AI_length]; omega
  simpa [highs,lows] using (append_parity (AI t) [Int.ofNat (3*t+2),Int.ofNat (3*t+3)]).1 even |>.1

theorem AI_low_step (t : Nat) : lows (AI (t+1)) = lows (AI t) ++ [Int.ofNat (3*t+3)] := by
  rw [AI_step]
  have even : (AI t).length%2=0 := by rw [AI_length]; omega
  simpa [highs,lows] using (append_parity (AI t) [Int.ofNat (3*t+2),Int.ofNat (3*t+3)]).1 even |>.2

theorem DI_high_step (t : Nat) : highs (DI (t+1)) = Int.ofNat (3*t+4)::highs (DI t) := by
  rw [DI_step]; rfl
theorem DI_low_step (t : Nat) : lows (DI (t+1)) = Int.ofNat (3*t+2)::lows (DI t) := by
  rw [DI_step]; rfl

def stair (t : Nat) : List Int :=
  [Int.ofNat (3*t+2),Int.ofNat (3*t+3),Int.ofNat (3*t+4),Int.ofNat (3*t+2)]

theorem valley_parts (t : Nat) :
    valley t=LI t ++ ([0] ++ (AI t ++ (stair t ++ DI t))) := by
  simp [valley,LI,AI,DI,stair,List.map_append,List.append_assoc]

theorem valley_high_parts (t : Nat) :
    highs (valley t)=highs (LI t) ++ [0] ++ lows (AI t) ++
      [Int.ofNat (3*t+3),Int.ofNat (3*t+2)] ++ lows (DI t) := by
  rw [valley_parts]
  have eL : (LI t).length%2=0 := by rw [LI_length]; omega
  rw [((append_parity (LI t) ([0] ++ (AI t ++ (stair t ++ DI t)))).1 eL).1]
  simp only [List.singleton_append]
  rw [highs_cons]
  have eA : (AI t).length%2=0 := by rw [AI_length]; omega
  rw [((append_parity (AI t) (stair t ++ DI t)).1 eA).2]
  have eS : (stair t).length%2=0 := by simp [stair]
  rw [((append_parity (stair t) (DI t)).1 eS).2]
  simp [stair,lows,List.append_assoc]

theorem valley_low_parts (t : Nat) :
    lows (valley t)=lows (LI t) ++ highs (AI t) ++
      [Int.ofNat (3*t+2),Int.ofNat (3*t+4)] ++ highs (DI t) := by
  rw [valley_parts]
  have eL : (LI t).length%2=0 := by rw [LI_length]; omega
  rw [((append_parity (LI t) ([0] ++ (AI t ++ (stair t ++ DI t)))).1 eL).2]
  simp only [List.singleton_append]
  rw [lows_cons]
  have eA : (AI t).length%2=0 := by rw [AI_length]; omega
  rw [((append_parity (AI t) (stair t ++ DI t)).1 eA).1]
  have eS : (stair t).length%2=0 := by simp [stair]
  rw [((append_parity (stair t) (DI t)).1 eS).1]
  simp [stair,highs,List.append_assoc]

theorem valley_high_increment (t : Nat) :
    (highs (valley (t+1))).Perm
      (highs (valley t) ++
        [Int.ofNat (3*t+4),Int.ofNat (3*t+5),Int.ofNat (3*t+6)]) := by
  apply List.perm_iff_count.mpr
  intro x
  have e2 : 3*(t+1)+2=3*t+5 := by omega
  have e3 : 3*(t+1)+3=3*t+6 := by omega
  simp [valley_high_parts, LI_high_step, AI_low_step, DI_low_step, e2, e3,
    List.count_append, List.count_cons]
  omega

theorem valley_low_increment (t : Nat) :
    (lows (valley (t+1))).Perm
      (lows (valley t) ++
        [Int.ofNat (3*t+3),Int.ofNat (3*t+5),Int.ofNat (3*t+7)]) := by
  apply List.perm_iff_count.mpr
  intro x
  have e2 : 3*(t+1)+2=3*t+5 := by omega
  have e4 : 3*(t+1)+4=3*t+7 := by omega
  simp [valley_low_parts, LI_low_step, AI_high_step, DI_high_step, e2, e4,
    List.count_append, List.count_cons]
  omega

theorem edgeSums_append_last (xs : List Int) (a b : Int) (ys : List Int) :
    edgeSums ((xs ++ [a]) ++ b::ys) =
      edgeSums (xs ++ [a]) ++ (a+b)::edgeSums (b::ys) := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    cases xs with
    | nil => simp [edgeSums]
    | cons d zs => simpa [edgeSums,List.append_assoc] using ih

theorem edgeSums_append_nonempty (xs : List Int) (hx : xs ≠ []) (b : Int) (ys : List Int) :
    edgeSums (xs ++ b::ys) =
      edgeSums xs ++ (xs.getLast hx+b)::edgeSums (b::ys) := by
  have decomp := List.dropLast_concat_getLast hx
  calc
    edgeSums (xs ++ b::ys) =
        edgeSums ((xs.dropLast ++ [xs.getLast hx]) ++ b::ys) := by rw [decomp]
    _ = edgeSums (xs.dropLast ++ [xs.getLast hx]) ++
          (xs.getLast hx+b)::edgeSums (b::ys) := edgeSums_append_last _ _ _ _
    _ = edgeSums xs ++ (xs.getLast hx+b)::edgeSums (b::ys) := by rw [decomp]

theorem sums_join (xs ys : List Int) (a b : Int)
    (ha : xs.getLast?=some a) (hb : ys.head?=some b) :
    edgeSums (xs++ys)=edgeSums xs ++ [a+b] ++ edgeSums ys := by
  have ne : xs ≠ [] := by intro eq; simp [eq] at ha
  have last : xs.getLast ne=a := by
    rw [List.getLast?_eq_some_getLast ne] at ha
    exact Option.some.inj ha
  obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp hb
  subst ys
  rw [edgeSums_append_nonempty xs ne b tail,last]
  simp [List.append_assoc]

theorem LI_last (t : Nat) : (LI t).getLast?=some 0 := by
  induction t with
  | zero => decide
  | succ t ih =>
    have ne : LI t ≠ [] := by
      intro eq
      have len := LI_length t
      simp [eq] at len
    rw [LI_step]
    simp [List.getLast?_cons_of_ne_nil ne, ih]

theorem LI_head (t : Nat) : (LI t).head?=some (Int.ofNat (3*t+1)) := by
  cases t with
  | zero => decide
  | succ t => simp [LI_step]; omega

theorem AI_head (t : Nat) : (AI (t+1)).head?=some 2 := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [AI_step (t+1), List.head?_append]
    simp [ih]

theorem AI_last (t : Nat) : (AI (t+1)).getLast?=some (Int.ofNat (3*t+3)) := by
  simp [AI_step]

theorem DI_head (t : Nat) : (DI t).head?=some (Int.ofNat (3*t+1)) := by
  cases t with
  | zero => decide
  | succ t => simp [DI_step]; omega

theorem DI_last (t : Nat) : (DI t).getLast?=some 1 := by
  induction t with
  | zero => decide
  | succ t ih =>
    have ne : DI t ≠ [] := by
      intro eq
      have len := DI_length t
      simp [eq] at len
    rw [DI_step]
    simp [List.getLast?_cons_of_ne_nil ne, ih]

theorem valley_first_all (t : Nat) :
    (valley t).head?=some (Int.ofNat (3*t+1)) := by
  rw [valley_parts]
  simp [List.head?_append,LI_head]

theorem valley_terminal_all (t : Nat) :
    (valley t)[6*t+7]?=some 1 := by
  have last : (valley t).getLast?=some 1 := by
    have eq : valley t =
        (((LI t ++ [0]) ++ AI t) ++ stair t) ++ DI t := by
      rw [valley_parts]; simp [List.append_assoc]
    rw [eq,List.getLast?_append,DI_last]
    rfl
  rw [List.getLast?_eq_getElem?,valley_length] at last
  simpa [show 6*t+8-1=6*t+7 by omega] using last

theorem LI_sum_step (t : Nat) :
    edgeSums (LI (t+1)) =
      [Int.ofNat (6*t+7),Int.ofNat (6*t+4)] ++ edgeSums (LI t) := by
  obtain ⟨xs,eq⟩ := List.head?_eq_some_iff.mp (LI_head t)
  rw [LI_step,eq]
  simp [edgeSums]
  congr 1 <;> omega

theorem DI_sum_step (t : Nat) :
    edgeSums (DI (t+1)) =
      [Int.ofNat (6*t+6),Int.ofNat (6*t+3)] ++ edgeSums (DI t) := by
  obtain ⟨xs,eq⟩ := List.head?_eq_some_iff.mp (DI_head t)
  rw [DI_step,eq]
  simp [edgeSums]
  congr 1 <;> omega

theorem AI_sum_step (s : Nat) :
    edgeSums (AI (s+2)) = edgeSums (AI (s+1)) ++
      [Int.ofNat (6*s+8),Int.ofNat (6*s+11)] := by
  let old := AI (s+1)
  have ne : old ≠ [] := by
    intro eq
    have len := AI_length (s+1)
    simp [old,eq] at len
  have last : old.getLast ne=Int.ofNat (3*s+3) := by
    have opt := AI_last s
    rw [List.getLast?_eq_some_getLast ne] at opt
    exact Option.some.inj opt
  have idx : s+2=(s+1)+1 := by omega
  rw [idx,AI_step]
  change edgeSums (old ++ (Int.ofNat (3*(s+1)+2))::[Int.ofNat (3*(s+1)+3)]) = _
  rw [edgeSums_append_nonempty old ne]
  simp [edgeSums,last]
  dsimp [old]
  have e1 : 3*(s:Int)+3+(3*((s:Int)+1)+2)=6*(s:Int)+8 := by omega
  have e2 : 3*((s:Int)+1)+2+(3*((s:Int)+1)+3)=6*(s:Int)+11 := by omega
  rw [e1,e2]

theorem valley_sum_parts (s : Nat) :
    edgeSums (valley (s+1)) =
      edgeSums (LI (s+1)) ++ [0,2] ++ edgeSums (AI (s+1)) ++
      [Int.ofNat (6*(s+1)+2),Int.ofNat (6*(s+1)+5),
       Int.ofNat (6*(s+1)+7),Int.ofNat (6*(s+1)+6),
       Int.ofNat (6*(s+1)+3)] ++ edgeSums (DI (s+1)) := by
  let t := s+1
  let X := LI t ++ [0]
  let Y := X ++ AI t
  let Z := Y ++ stair t
  have veq : valley t=Z++DI t := by
    simp [Z,Y,X,valley_parts,List.append_assoc]
  have lx : X.getLast?=some 0 := by simp [X]
  have ay : (AI t).head?=some 2 := by simpa [t] using AI_head s
  have ly : Y.getLast?=some (Int.ofNat (3*s+3)) := by
    simp [Y,List.getLast?_append,AI_last,t]
  have hs : (stair t).head?=some (Int.ofNat (3*t+2)) := by simp [stair]
  have lz : Z.getLast?=some (Int.ofNat (3*t+2)) := by
    simp [Z,List.getLast?_append,stair]
  have hd : (DI t).head?=some (Int.ofNat (3*t+1)) := DI_head t
  have j1 := sums_join (LI t) [0] 0 0 (LI_last t) (by rfl)
  have j2 := sums_join X (AI t) 0 2 lx ay
  have j3 := sums_join Y (stair t) (Int.ofNat (3*s+3)) (Int.ofNat (3*t+2)) ly hs
  have j4 := sums_join Z (DI t) (Int.ofNat (3*t+2)) (Int.ofNat (3*t+1)) lz hd
  rw [veq,j4,j3,j2,j1]
  simp [t,stair,edgeSums,List.append_assoc]
  congr 1 <;> omega

theorem valley_sum_increment (s : Nat) :
    (edgeSums (valley (s+2))).Perm
      (edgeSums (valley (s+1)) ++
       [Int.ofNat (6*(s+1)+4),Int.ofNat (6*(s+1)+8),
        Int.ofNat (6*(s+1)+9),Int.ofNat (6*(s+1)+11),
        Int.ofNat (6*(s+1)+12),Int.ofNat (6*(s+1)+13)]) := by
  apply List.perm_iff_count.mpr
  intro x
  have old := valley_sum_parts s
  have new := valley_sum_parts (s+1)
  simp only [show (s+1)+1=s+2 by omega] at new
  rw [new,old]
  rw [LI_sum_step (s+1), AI_sum_step s, DI_sum_step (s+1)]
  have a1 : 6*s+8=6*(s+1)+2 := by omega
  have a2 : 6*s+11=6*(s+1)+5 := by omega
  have b2 : 6*(s+2)+2=6*(s+1)+8 := by omega
  have b3 : 6*(s+2)+3=6*(s+1)+9 := by omega
  have b5 : 6*(s+2)+5=6*(s+1)+11 := by omega
  have b6 : 6*(s+2)+6=6*(s+1)+12 := by omega
  have b7 : 6*(s+2)+7=6*(s+1)+13 := by omega
  simp [a1,a2,b2,b3,b5,b6,b7,List.count_append,List.count_cons]
  omega

theorem valley_sum_increment_pos (t : Nat) (ht : 1≤t) :
    (edgeSums (valley (t+1))).Perm
      (edgeSums (valley t) ++
       [Int.ofNat (6*t+4),Int.ofNat (6*t+8),Int.ofNat (6*t+9),
        Int.ofNat (6*t+11),Int.ofNat (6*t+12),Int.ofNat (6*t+13)]) := by
  have eq : t-1+1=t := by omega
  have eq2 : t-1+2=t+1 := by omega
  simpa [eq,eq2] using valley_sum_increment (t-1)

theorem band_succ3 (n : Nat) :
    band (n+3)=band n ++ [Int.ofNat n,Int.ofNat (n+1),Int.ofNat (n+2)] := by
  simp [band,List.range_succ,List.append_assoc]

theorem band_succ6 (n : Nat) :
    band (n+6)=band n ++
      [Int.ofNat n,Int.ofNat (n+1),Int.ofNat (n+2),
       Int.ofNat (n+3),Int.ofNat (n+4),Int.ofNat (n+5)] := by
  simp [show n+6=(n+3)+3 by omega,band_succ3,List.append_assoc]
  omega

theorem valley_high_band_step (t : Nat)
    (old : (highs (valley t)).Perm (band (3*t+4))) :
    (highs (valley (t+1))).Perm (band (3*(t+1)+4)) := by
  apply List.perm_iff_count.mpr
  intro x
  have inc := (valley_high_increment t).count_eq x
  have prev := old.count_eq x
  have e0 : 3*(t+1)+4=(3*t+4)+3 := by omega
  have e1 : (3*t+4)+1=3*t+5 := by omega
  have e2 : (3*t+4)+2=3*t+6 := by omega
  simp [e0,band_succ3,e1,e2,List.count_append,List.count_cons] at inc prev ⊢
  omega

theorem valley_low_band_step (t : Nat)
    (old : (lows (valley t)).Perm
      (band (3*t+3) ++ [Int.ofNat (3*t+4)])) :
    (lows (valley (t+1))).Perm
      (band (3*(t+1)+3) ++ [Int.ofNat (3*(t+1)+4)]) := by
  apply List.perm_iff_count.mpr
  intro x
  have inc := (valley_low_increment t).count_eq x
  have prev := old.count_eq x
  have e0 : 3*(t+1)+3=(3*t+3)+3 := by omega
  have e1 : (3*t+3)+1=3*t+4 := by omega
  have e2 : (3*t+3)+2=3*t+5 := by omega
  have e3 : 3*(t+1)+4=3*t+7 := by omega
  simp [e0,e1,e2,e3,band_succ3,List.count_append,List.count_cons] at inc prev ⊢
  omega

theorem valley_sum_band_step (t : Nat) (ht : 1≤t)
    (old : (edgeSums (valley t)).Perm
      (band (6*t+4) ++ [Int.ofNat (6*t+5),Int.ofNat (6*t+6),Int.ofNat (6*t+7)])) :
    (edgeSums (valley (t+1))).Perm
      (band (6*(t+1)+4) ++
       [Int.ofNat (6*(t+1)+5),Int.ofNat (6*(t+1)+6),Int.ofNat (6*(t+1)+7)]) := by
  apply List.perm_iff_count.mpr
  intro x
  have inc := (valley_sum_increment_pos t ht).count_eq x
  have prev := old.count_eq x
  have e0 : 6*(t+1)+4=(6*t+4)+6 := by omega
  have e1 : (6*t+4)+1=6*t+5 := by omega
  have e2 : (6*t+4)+2=6*t+6 := by omega
  have e3 : (6*t+4)+3=6*t+7 := by omega
  have e4 : (6*t+4)+4=6*t+8 := by omega
  have e5 : (6*t+4)+5=6*t+9 := by omega
  have f5 : 6*(t+1)+5=6*t+11 := by omega
  have f6 : 6*(t+1)+6=6*t+12 := by omega
  have f7 : 6*(t+1)+7=6*t+13 := by omega
  simp [e0,e1,e2,e3,e4,e5,f5,f6,f7,band_succ6,
    List.count_append,List.count_cons] at inc prev ⊢
  omega

theorem valley_contract_step (t : Nat) (ht : 5≤t) (hc : ValleyContract t) :
    ValleyContract (t+1) :=
  ⟨valley_length (t+1),valley_first_all (t+1),valley_terminal_all (t+1),
   valley_high_band_step t hc.lowSide,
   valley_low_band_step t hc.highSide,
   valley_sum_band_step t (by omega) hc.sums,
   valley_zeros (t+1)⟩

theorem valley_contract_all (t : Nat) (ht : 5≤t) : ValleyContract t := by
  have all : ∀d : Nat, ValleyContract (d+5) := by
    intro d
    induction d with
    | zero => simpa using valley5_valid
    | succ d ih =>
      simpa [Nat.succ_eq_add_one,Nat.add_assoc] using
        valley_contract_step (d+5) (by omega) ih
  have eq : t-5+5=t := by omega
  simpa [eq] using all (t-5)

end GracefulSignedCap
