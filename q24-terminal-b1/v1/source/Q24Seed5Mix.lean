import Q24MixFamily
namespace GracefulBoundary.Q24Seed5Mix
open P20Q24

def seed5 : List Nat := [11,12,13,6,1,0,0,2,4,5,3,1,2,3,8,14,16,15,14,13,15,11,10,22,23,21,22,20,21,19,20,18,19,17,18,16,17,7,5,10,7,9,9,4,6,8,12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem seed5_state : State 23 5 seed5 := by constructor <;> decide

/-- True selects B4; the tail is executed before the head. Every finite order occurs. -/
def word : List Bool → List Nat
  | [] => seed5
  | b::bs => if b then Q24B4.extend (5+2*bs.length+2*bs.count true) (word bs)
             else P20Q24.extend (5+2*bs.length+2*bs.count true) (word bs)

theorem all_states (bs : List Bool) :
    State (23+24*bs.length) (5+2*bs.length+2*bs.count true) (word bs) := by
  induction bs with
  | nil => exact seed5_state
  | cons b bs ih =>
    cases b with
    | false =>
      have h := P20Q24.q24_preserves_state _ _ _ ih
      simpa [word, List.count_cons,
        show 23+24*bs.length+24=23+24*(bs.length+1) by omega,
        show 5+2*bs.length+2*bs.count true+2=5+2*(bs.length+1)+2*bs.count true by omega] using h
    | true =>
      have h := Q24B4.q24_preserves_state _ _ _ ih
      simpa [word, List.count_cons,
        show 23+24*bs.length+24=23+24*(bs.length+1) by omega,
        show 5+2*bs.length+2*bs.count true+4=5+2*(bs.length+1)+2*(bs.count true+1) by omega] using h

theorem family_certificate (bs : List Bool) :
    FiniteAlpha.Certificate (10+12*bs.length)
      (18+22*bs.length-2*bs.count true) (17+22*bs.length-2*bs.count true)
      (coreLabels (46+48*bs.length) (word bs)) := by
  have h := all_states bs
  have hj : bs.count true≤bs.length := List.count_le_length
  have k : 2*(10+12*bs.length)+3=23+24*bs.length := by omega
  have k1 : 2*(10+12*bs.length)+4=23+24*bs.length+1 := by omega
  have M : 4*(10+12*bs.length)+6=46+48*bs.length := by omega
  have mid : 2*(10+12*bs.length)+2=23+24*bs.length-1 := by omega
  have generic := WholeTagged.whole_path_certificate (10+12*bs.length) (word bs)
    (by rw [k]; exact h.length) (by rw [k1]; exact h.high)
    (by rw [k]; exact h.low)
    (by rw [show 4*(10+12*bs.length)+6=2*(23+24*bs.length) by omega]; exact h.sums)
    (by rw [k,mid]; exact h.midpoint)
  rw [M] at generic
  refine ⟨by omega,by omega,by omega,by omega,generic,?_,?_⟩
  · rw [show 2*(10+12*bs.length)+3-(18+22*bs.length-2*bs.count true)=5+2*bs.length+2*bs.count true by omega,
      coreLabels_lookup,h.lowZero]
    simp only [show ¬(5+2*bs.length+2*bs.count true)%2=0 by omega,ite_false,Option.map_some]
  · rw [show 2*(10+12*bs.length)+3-(17+22*bs.length-2*bs.count true)=5+2*bs.length+2*bs.count true+1 by omega,
      coreLabels_lookup,h.highZero]
    simp only [show (5+2*bs.length+2*bs.count true+1)%2=0 by omega,ite_true,Option.map_some,Nat.sub_zero,M]

/-- Separate labelings at both depths, after any actual finite B2/B4 order. -/
theorem order_actual (bs : List Bool) (n m : Nat) (hn : 2≤n) (a : Fin n) :
    DepthZero n m (23+24*bs.length) (18+22*bs.length-2*bs.count true) a ∧
    DepthZero n m (23+24*bs.length) (17+22*bs.length-2*bs.count true) a := by
  have hj : bs.count true≤bs.length := List.count_le_length
  have result := FiniteAlpha.prescribed_zero (10+12*bs.length)
    (18+22*bs.length-2*bs.count true) (17+22*bs.length-2*bs.count true) n m
    (coreLabels (46+48*bs.length) (word bs)) (family_certificate bs) hn a
  have lifted : DepthZero n m (2*(10+12*bs.length)+3) (18+22*bs.length-2*bs.count true) a ∧
      DepthZero n m (2*(10+12*bs.length)+3) (17+22*bs.length-2*bs.count true) a := by
    obtain ⟨f,hf,hz⟩ := result.1
    obtain ⟨g,hg,hm⟩ := result.2
    exact ⟨⟨by omega,f,hf,hz⟩,⟨by omega,g,hg,hm⟩⟩
  simpa only [show 2*(10+12*bs.length)+3=23+24*bs.length by omega] using lifted

theorem interval_choice (t d : Nat) (hd : 17+20*t≤d ∧ d≤18+22*t) :
    ∃ j, j≤t ∧ (d=17+22*t-2*j ∨ d=18+22*t-2*j) := by
  refine ⟨(18+22*t-d)/2,?_,?_⟩
  · omega
  · have hmod := Nat.mod_lt (18+22*t-d) (by decide : 0<2)
    omega

theorem count_order_actual (t j n m : Nat) (hj : j≤t) (hn : 2≤n) (a : Fin n) :
    DepthZero n m (23+24*t) (18+22*t-2*j) a ∧
    DepthZero n m (23+24*t) (17+22*t-2*j) a := by
  have result := order_actual (List.replicate j true ++ List.replicate (t-j) false) n m hn a
  have lengthEq : (List.replicate j true ++ List.replicate (t-j) false).length=t := by simp; omega
  have countEq : (List.replicate j true ++ List.replicate (t-j) false).count true=j := by simp [List.count_replicate]
  simpa only [lengthEq,countEq] using result

/-- Exact all-t interval, any actual named arm, all n≥2 and original m≥0 leaves. -/
theorem interval_actual (t n m d : Nat) (hn : 2≤n) (a : Fin n)
    (hd : 17+20*t≤d ∧ d≤18+22*t) :
    ∃ (hlt : d-1<23+24*t) (f : SpiderVertex n m (23+24*t) → Nat),
      Graceful (spiderGraph n m (23+24*t)) (n*(23+24*t)+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 := by
  obtain ⟨j,hj,hlo|hhi⟩ := interval_choice t d hd
  · rw [hlo]
    exact (count_order_actual t j n m hj hn a).2
  · rw [hhi]
    exact (count_order_actual t j n m hj hn a).1

/-- Separately gated literal z5 seed combined with the P20 interval. -/
theorem combined_interval_actual (t n m d : Nat) (hn : 2≤n) (a : Fin n)
    (hd : 17+20*t≤d ∧ d≤20+22*t) :
    ∃ (hlt : d-1<23+24*t) (f : SpiderVertex n m (23+24*t) → Nat),
      Graceful (spiderGraph n m (23+24*t)) (n*(23+24*t)+m) f ∧
      f (.arm a ⟨d-1,hlt⟩)=0 := by
  by_cases h : 19+20*t≤d
  · exact Q24Mix.interval_actual t n m d hn a ⟨h,hd.2⟩
  · exact interval_actual t n m d hn a ⟨hd.1,by omega⟩
end GracefulBoundary.Q24Seed5Mix
