import GraftExtreme
namespace GracefulBoundary.Scattered
open EvenBoundary.Flexible

def PrefixFacts (R q : Nat) : Prop :=
  (retained R q).length=2*(R-q+2)-3 ∧
  (highs (retained R q)).Perm (List.range' q (R-q)++[R-q+2+q-2+1]) ∧
  (lows (retained R q)).Perm (List.range' q (R-q)) ∧
  (edgeSums (retained R q++[q-2])).Perm (List.range' (2*q-1) (2*(R-q+2)-3)) ∧
  (retained R q).head?=some (R-q+2+q-2+1)
instance (R q : Nat) : Decidable (PrefixFacts R q) := by unfold PrefixFacts; infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem prefix_matrix : ∀R,R∈radii → ∀q,q∈([9,11,12] : List Nat) → PrefixFacts R q := by decide

theorem radius_lower (R : Nat) (hR : R∈radii) : 14≤R := by
  simp [radii] at hR
  omega

theorem prefix_contract (R q : Nat) (hR : R∈radii) (hq : q∈([9,11,12] : List Nat)) :
    TailGraft.RetainedPrefix (R-q+2) q (retained R q) := by
  have hr := radius_lower R hR
  have qbound : q≤12 := by simp at hq; omega
  rcases prefix_matrix R hR q hq with ⟨hlen,hlow,hhigh,hsum,hfirst⟩
  have eq : R-q+2-2=R-q := by omega
  exact ⟨hlen,by simpa only [eq] using hlow,by simpa only [eq] using hhigh,hsum,hfirst⟩

theorem listed_graft (R q deficit : Nat) (hR : R∈radii) (hq : q∈([9,11,12] : List Nat)) (u : List Nat)
    (hc : ExtremePacket q deficit ((q+1)::(q-2)::u)) : ∃c,ExtremePacket R deficit c := by
  have hr := radius_lower R hR
  have qbound : 2≤q ∧ q≤12 := by simp at hq; omega
  have next := supplied_extreme_graft (R-q+2) q deficit (by omega) qbound.1 (retained R q) u (prefix_contract R q hR hq) hc
  have size : R-q+2+q-2=R := by omega
  simpa only [size] using (show ∃c,ExtremePacket (R-q+2+q-2) deficit c from ⟨_,next⟩)

theorem q11_high13 : ExtremePacket 11 13 FullFixed26.seedHigh11 := by
  refine ⟨FullFixed26.seedHigh11_core,by decide,by decide,?_⟩; intro N; rfl
theorem q11_low14 : ExtremePacket 11 14 FullFixed26.seedLow11 := by
  refine ⟨FullFixed26.seedLow11_core,by decide,by decide,?_⟩; intro N; rfl
theorem q12_high15 : ExtremePacket 12 15 FullFixed28.seed12 := by
  refine ⟨FullFixed28.seed12_core,by decide,by decide,?_⟩; intro N; rfl
theorem q12_low16 : ExtremePacket 12 16 FullFixed28.seed12 := by
  refine ⟨FullFixed28.seed12_core,by decide,by decide,?_⟩; intro N; rfl

/-- Every deficit in the complete band, on every listed radius, from explicit graft interfaces. -/
theorem listed_deficit_band (R deficit : Nat) (hR : R∈radii) (hd : 9≤deficit ∧ deficit≤16) :
    ∃c,ExtremePacket R deficit c := by
  have cases : deficit=9 ∨ deficit=10 ∨ deficit=11 ∨ deficit=12 ∨ deficit=13 ∨ deficit=14 ∨ deficit=15 ∨ deficit=16 := by omega
  rcases cases with h|h|h|h|h|h|h|h <;> subst deficit
  · exact listed_graft R 9 9 hR (by decide) _ FullFixed.c10r9_odd
  · exact listed_graft R 9 10 hR (by decide) _ FullFixed.c10r9_even
  · exact listed_graft R 9 11 hR (by decide) _ FullFixed26.low9_c11
  · exact listed_graft R 9 12 hR (by decide) _ FullFixed26.low9_c12
  · exact listed_graft R 11 13 hR (by decide) _ q11_high13
  · exact listed_graft R 11 14 hR (by decide) _ q11_low14
  · exact listed_graft R 12 15 hR (by decide) _ q12_high15
  · exact listed_graft R 12 16 hR (by decide) _ q12_low16

def tipList (R : Nat) : List Nat := R::(List.range R).reverse.flatMap (fun x => [x,x])
def TipFacts (R : Nat) : Prop :=
  (tipList R).length=2*R+1 ∧ (highs (tipList R)).Perm (List.range R++[R]) ∧
  (lows (tipList R)).Perm (List.range R) ∧ (edgeSums (tipList R)).Perm (List.range (2*R)) ∧
  (tipList R).head?=some R ∧ (tipList R)[2*R]?=some 0
instance (R : Nat) : Decidable (TipFacts R) := by unfold TipFacts; infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem tip_matrix : ∀R,R∈radii → TipFacts R := by decide

theorem listed_tip_contract (R : Nat) (hR : R∈radii) :
    FullFixed.RootZeroTip.CorePacket R (tipList R) ∧ ∀N,(decode N false (tipList R))[2*R]?=some 0 := by
  rcases tip_matrix R hR with ⟨hlen,hlow,hhigh,hsum,hfirst,hzero⟩
  refine ⟨⟨hlen,hlow,hhigh,hsum,hfirst⟩,?_⟩
  intro N
  simpa [show (2*R)%2=0 by omega] using decode_zero_lookup N (2*R) false (tipList R) hzero

theorem lengths_radii : lengths=radii.map (fun R => 2*R) := by decide
theorem listed_radius (k : Nat) (hk : k∈lengths) : ∃R,R∈radii ∧ k=2*R := by
  rw [lengths_radii] at hk
  obtain ⟨R,hR,eq⟩ := List.mem_map.mp hk
  exact ⟨R,hR,eq.symm⟩

theorem finite_arithmetic_gate : ∀k,k∈lengths → 19≤k ∧ k%2=0 ∧ k-17≤GapFill.depthPrefix k := by decide

end GracefulBoundary.Scattered
