import AllEvenTheorem
namespace GracefulBoundary.EvenBoundary
open EvenUniform

theorem decoded_alpha_sides (N A : Nat) (c : List Nat) :
    ((∀x∈highs c,x≤A) → (∀x∈lows c,A<N-x) → crosses A (decode N false c)) ∧
    ((∀x∈highs c,A<N-x) → (∀x∈lows c,x≤A) → crosses A (decode N true c)) := by
  induction c using edgeSums.induct with
  | case1 => constructor <;> intro _ _ <;> trivial
  | case2 a => constructor <;> intro _ _ <;> trivial
  | case3 a b c ih =>
    constructor
    · intro hl hh
      have ha := hl a (List.mem_cons_self)
      have hb := hh b (List.mem_cons_self)
      have tl : ∀x∈lows (b::c),x≤A := by intro x hx; rw [lows_cons] at hx; exact hl x (List.mem_cons_of_mem a hx)
      have th : ∀x∈highs (b::c),A<N-x := by intro x hx; apply hh x; rw [lows_cons]; exact hx
      change cross A a (N-b) ∧ crosses A (decode N true (b::c))
      exact ⟨Or.inl ⟨ha,hb⟩,ih.2 th tl⟩
    · intro hh hl
      have ha := hh a (List.mem_cons_self)
      have hb := hl b (List.mem_cons_self)
      have th : ∀x∈lows (b::c),A<N-x := by intro x hx; rw [lows_cons] at hx; exact hh x (List.mem_cons_of_mem a hx)
      have tl : ∀x∈highs (b::c),x≤A := by intro x hx; apply hl x; rw [lows_cons]; exact hx
      change cross A (N-a) b ∧ crosses A (decode N false (b::c))
      exact ⟨Or.inr ⟨hb,ha⟩,ih.1 tl th⟩

theorem one_decoded_labels (r : Nat) (c : List Nat) (hc : Auxiliary r c) :
    (decode (2*r-1) false c).Perm ((0::List.range' 2 (r-1))++List.range' (r+1) (r-1)) := by
  have hr := hc.lower
  have high := hc.high.map (fun x => 2*r-1-x)
  have reflected := reflected_interval (2*r-1) 0 (r-1) (by omega)
  simp only [←List.range_eq_range',show 2*r-1+1-0-(r-1)=r+1 by omega] at reflected
  exact (decode_side_permutations (2*r-1) c).2.trans (hc.low.append (high.trans reflected))

theorem one_decoded_edges (r : Nat) (c : List Nat) (hc : Auxiliary r c) :
    (edgeDiffs (decode (2*r-1) false c)).Perm (List.range' 1 (2*r-2)) := by
  have hr := hc.lower
  have bounds : ∀s∈edgeSums c,s≤2*r-1 := by
    intro s hs
    obtain ⟨i,hi,he⟩ := List.mem_range'.mp (hc.sums.mem_iff.mp hs)
    omega
  rw [LabelOne.decode_sums _ c false bounds]
  have hp := hc.sums.map (fun x => 2*r-1-x)
  have reflected := reflected_interval (2*r-1) 1 (2*r-2) (by omega)
  rw [show 2*r-1+1-1-(2*r-2)=1 by omega] at reflected
  exact hp.trans reflected

theorem one_decoded_alpha (r : Nat) (c : List Nat) (hc : Auxiliary r c) : crosses r (decode (2*r-1) false c) := by
  apply (decoded_alpha_sides (2*r-1) r c).1
  · intro x hx
    have h := hc.low.mem_iff.mp hx
    simp only [List.mem_cons] at h
    rcases h with h|h
    · omega
    · obtain ⟨i,hi,he⟩ := List.mem_range'.mp h; omega
  · intro x hx
    have h := List.mem_range.mp (hc.high.mem_iff.mp hx)
    have hr := hc.lower
    omega

def oneArmPath (r : Nat) (c : List Nat) := [1,2*r]++decode (2*r-1) false c

theorem one_arm_certificate (r : Nat) (c : List Nat) (hc : Auxiliary r c) :
    (oneArmPath r c).length=2*r+1 ∧ (oneArmPath r c).Perm (List.range (2*r+1)) ∧
    (edgeDiffs (oneArmPath r c)).Perm (List.range' 1 (2*r)) ∧ crosses r (oneArmPath r c) ∧
    (oneArmPath r c)[0]?=some 1 ∧ (oneArmPath r c)[1]?=some (2*r) ∧ (oneArmPath r c)[2]?=some 0 := by
  have hr := hc.lower
  obtain ⟨tail,shape⟩ := List.head?_eq_some_iff.mp hc.first
  have decoded : decode (2*r-1) false c=0::decode (2*r-1) true tail := by rw [shape]; rfl
  refine ⟨?_,?_,?_,?_,rfl,rfl,?_⟩
  · simp only [oneArmPath,List.length_append,List.length_cons,List.length_nil,LabelOne.decode_length,hc.length]; omega
  · have hp := (List.Perm.refl [1,2*r]).append (one_decoded_labels r c hc)
    apply hp.trans
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.count_append,List.count_cons,List.count_nil,count_band,List.count_range,Nat.beq_eq_true_eq]
    repeat (any_goals (first | omega | split))
  · have edges : edgeDiffs (oneArmPath r c)=[2*r-1,2*r]++edgeDiffs (decode (2*r-1) false c) := by
      rw [oneArmPath,decoded]
      simp only [List.cons_append,List.nil_append,edgeDiffs]
      have h1 : distance 1 (2*r)=2*r-1 := by dsimp only [distance]; omega
      have h2 : distance (2*r) 0=2*r := by dsimp only [distance]; omega
      rw [h1,h2]
    rw [edges]
    apply ((List.Perm.refl _).append (one_decoded_edges r c hc)).trans
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.count_append,List.count_cons,List.count_nil,count_band,Nat.beq_eq_true_eq]
    repeat (any_goals (first | omega | split))
  · have ha := one_decoded_alpha r c hc
    rw [decoded] at ha
    rw [oneArmPath,decoded]
    change cross r 1 (2*r) ∧ cross r (2*r) 0 ∧ crosses r (0::decode (2*r-1) true tail)
    exact ⟨Or.inl ⟨by omega,by omega⟩,Or.inr ⟨by omega,by omega⟩,ha⟩
  · rw [oneArmPath,decoded]; rfl

theorem one_arm_anchored_alpha (r : Nat) (hr : 3≤r) :
    ∃ f : Fin (2*r+1) → Nat, Graceful (pathGraph (2*r)) (2*r) f ∧ Alpha (pathGraph (2*r)) r f ∧
      f ⟨0,by omega⟩=1 ∧ f ⟨1,by omega⟩=2*r ∧ f ⟨2,by omega⟩=0 := by
  obtain ⟨c,hc⟩ := auxiliaries r hr
  obtain ⟨len,hv,he,ha,h1,hmax,hzero⟩ := one_arm_certificate r c hc
  refine ⟨pathLabel (2*r) (oneArmPath r c),list_path_graceful (2*r) _ hv he,list_path_alpha (2*r) r _ len ha,?_,?_,?_⟩
  · simp [pathLabel,List.getD_eq_getElem?_getD,h1]
  · simp [pathLabel,List.getD_eq_getElem?_getD,hmax]
  · simp [pathLabel,List.getD_eq_getElem?_getD,hzero]

end GracefulBoundary.EvenBoundary
