import VariableInterval
import VariableIdentification
namespace GracefulBoundary.Variable

def PathCertificate (p d : Nat) (c : List Nat) : Prop :=
  GenericPathCertificate p c ∧ c[2*p+3-d]?=some 0 ∧ c[2*p+2-d]?=some (4*p+6)

def boundaryZero (p d : Nat) : Fin (4*p+7) := ⟨2*p+3-d,by omega⟩
def boundaryMaximum (p d : Nat) : Fin (4*p+7) := ⟨2*p+2-d,by omega⟩

theorem core_to_path (p d : Nat) (c : List Nat) (hc : AnchoredCore p d c) :
    PathCertificate p d (completePath p c) := by
  have hp := hc.size
  have hd := hc.depth
  have hi := hc.inside
  have he := hc.even
  have hb : BoundaryCore p c := ⟨by omega,hc.length,hc.high,hc.low,hc.sums,hc.first,hc.last⟩
  have hgeneric := boundary_shell_bridge p c hb
  have hz := complete_path_core_lookup p c (d-1) hc.length (by omega)
  have hm := complete_path_core_lookup p c d hc.length (by omega)
  rw [coreLabels_lookup,hc.zeroL] at hz
  rw [coreLabels_lookup,hc.zeroH] at hm
  have e1 : 2*p+2-(d-1)=2*p+3-d := by omega
  have hodd : ¬ (d-1)%2=0 := by omega
  simp only [e1,hodd,ite_false,Option.map_some] at hz
  simp only [he,ite_true,Option.map_some,Nat.sub_zero] at hm
  exact ⟨hgeneric,hz,hm⟩

theorem certificate_graph (p d : Nat) (c : List Nat) (hc : PathCertificate p d c) :
    Graceful (pathGraph (4*p+6)) (4*p+6) (pathLabel (4*p+6) c) ∧
    Alpha (pathGraph (4*p+6)) (2*p+2) (pathLabel (4*p+6) c) := by
  rcases hc.1 with ⟨hlen,hv,he,ha,_⟩
  exact ⟨list_path_graceful (4*p+6) c hv he,list_path_alpha (4*p+6) (2*p+2) c hlen ha⟩

theorem certificate_graph_anchors (p d : Nat) (c : List Nat) (hc : PathCertificate p d c) :
    pathLabel (4*p+6) c (boundaryCenter p)=2*p+2 ∧
    pathLabel (4*p+6) c (boundaryZero p d)=0 ∧
    pathLabel (4*p+6) c (boundaryMaximum p d)=4*p+6 := by
  have hm := hc.1.2.2.2.2
  have hz := hc.2.1
  have hx := hc.2.2
  simp [pathLabel,boundaryCenter,boundaryZero,boundaryMaximum,List.getD_eq_getElem?_getD,hm,hz,hx]

theorem certificate_graft (p d h m : Nat) (c : List Nat) (hc : PathCertificate p d c) :
    Graceful (boundaryGraftGraph p h m) (4*p+6+(h*(2*p+3)+m)) (boundaryGraftLabel p h m c) := by
  have hp := certificate_graph p d c hc
  have ha := certificate_graph_anchors p d c hc
  have hr := residual_gracefulness h m (p+1)
  have hk : 2*(p+1)+1=2*p+3 := by omega
  rw [hk] at hr
  exact graceful_graft (pathGraph (4*p+6)) (spiderGraph h m (2*p+3))
    (boundaryCenter p) SpiderVertex.center (pathLabel (4*p+6) c) (residualLabel h m (2*p+3))
    (2*p+2) (4*p+6) (h*(2*p+3)+m) hp.1 hr ha.1 rfl hp.2

theorem certificate_graft_anchors (p d h m : Nat) (c : List Nat) (hc : PathCertificate p d c) :
    boundaryGraftLabel p h m c (graftEmbed (boundaryCenter p) SpiderVertex.center (boundaryZero p d))=0 ∧
    boundaryGraftLabel p h m c (graftEmbed (boundaryCenter p) SpiderVertex.center (boundaryMaximum p d))=
      4*p+6+(h*(2*p+3)+m) := by
  have ha := certificate_graph_anchors p d c hc
  constructor
  · exact graft_zero_anchor (boundaryCenter p) SpiderVertex.center (pathLabel (4*p+6) c)
      (residualLabel h m (2*p+3)) (2*p+2) (h*(2*p+3)+m) ha.1 rfl (boundaryZero p d) ha.2.1
  · exact graft_max_anchor (boundaryCenter p) SpiderVertex.center (pathLabel (4*p+6) c)
      (residualLabel h m (2*p+3)) (2*p+2) (4*p+6) (h*(2*p+3)+m) ha.1 rfl
      (by omega) (boundaryMaximum p d) ha.2.2

theorem zero_anchor_identification (p d h m : Nat) (hd : 2 ≤ d) (hi : d+1 < 2*p) :
    spiderToGraft p h m (.arm ⟨0,by omega⟩ ⟨d-1,by omega⟩) =
      graftEmbed (boundaryCenter p) SpiderVertex.center (boundaryZero p d) := by
  simp only [spiderToGraft,dite_true]
  have he : boundaryZero p d = (leftVertex p ⟨d-1,by omega⟩).val := by
    apply Fin.ext; dsimp only [boundaryZero,leftVertex]; omega
  rw [he,embed_left]

theorem maximum_anchor_identification (p d h m : Nat) (hi : d+1 < 2*p) :
    spiderToGraft p h m (.arm ⟨0,by omega⟩ ⟨d,by omega⟩) =
      graftEmbed (boundaryCenter p) SpiderVertex.center (boundaryMaximum p d) := by
  simp only [spiderToGraft,dite_true]
  have he : boundaryMaximum p d = (leftVertex p ⟨d,by omega⟩).val := by
    apply Fin.ext; rfl
  rw [he,embed_left]

theorem core_first_arm_spiders (p d h m : Nat) (c : List Nat) (hc : AnchoredCore p d c) :
    ∃ f : SpiderVertex (h+2) m (2*p+3) → Nat,
      Graceful (spiderGraph (h+2) m (2*p+3)) ((h+2)*(2*p+3)+m) f ∧
      f (.arm ⟨0,by omega⟩ ⟨d-1,by have := hc.inside; omega⟩)=0 ∧
      f (.arm ⟨0,by omega⟩ ⟨d,by have := hc.inside; omega⟩)=((h+2)*(2*p+3)+m) := by
  have hpath := core_to_path p d c hc
  let f := boundaryGraftLabel p h m (completePath p c)
  have hf := certificate_graft p d h m (completePath p c) hpath
  obtain ⟨hzero,hmax⟩ := certificate_graft_anchors p d h m (completePath p c) hpath
  have hg := graft_graceful_on_spider p h m _ f hf
  have hm : 4*p+6+(h*(2*p+3)+m)=(h+2)*(2*p+3)+m := by
    simp only [Nat.add_mul]; omega
  rw [hm] at hg hmax
  refine ⟨fun v => f (spiderToGraft p h m v),hg,?_,?_⟩
  · dsimp only; rw [zero_anchor_identification p d h m hc.depth hc.inside]; exact hzero
  · dsimp only; rw [maximum_anchor_identification p d h m hc.inside]; exact hmax

theorem core_selected_arm (p d n m : Nat) (c : List Nat) (hc : AnchoredCore p d c)
    (hn : 2 ≤ n) (a : Fin n) :
    ∃ f : SpiderVertex n m (2*p+3) → Nat,
      Graceful (spiderGraph n m (2*p+3)) (n*(2*p+3)+m) f ∧
      f (.arm a ⟨d-1,by have := hc.inside; omega⟩)=0 ∧
      f (.arm a ⟨d,by have := hc.inside; omega⟩)=n*(2*p+3)+m := by
  obtain ⟨h,rfl⟩ : ∃ h,n=h+2 := ⟨n-2,by omega⟩
  obtain ⟨f,hf,hzero,hmax⟩ := core_first_arm_spiders p d h m c hc
  let z : Fin (h+2) := ⟨0,by omega⟩
  refine ⟨fun v => f (swapVertex a z v),graceful_swap a z f hf,?_,?_⟩
  · simpa only [swapVertex,swapIndex_first] using hzero
  · simpa only [swapVertex,swapIndex_first] using hmax

/-- Arbitrary anchored balanced core to the actual spider at either paired depth. -/
theorem core_prescribed_zero (p d n m v : Nat) (c : List Nat) (hc : AnchoredCore p d c)
    (hn : 2 ≤ n) (hv : v=d ∨ v=d+1) (a : Fin n) :
    ∃ (hlt : v-1 < 2*p+3) (f : SpiderVertex n m (2*p+3) → Nat),
      Graceful (spiderGraph n m (2*p+3)) (n*(2*p+3)+m) f ∧
      f (.arm a ⟨v-1,hlt⟩)=0 := by
  obtain ⟨f,hf,hzero,hmax⟩ := core_selected_arm p d n m c hc hn a
  have hi := hc.inside
  cases hv with
  | inl hv => subst v; exact ⟨by omega,f,hf,hzero⟩
  | inr hv =>
    subst v
    refine ⟨by omega,fun x => n*(2*p+3)+m-f x,graceful_complement _ _ f hf,?_⟩
    simp only [Nat.add_sub_cancel,hmax,Nat.sub_self]

/-- Theorem A: every advertised integer depth, on every chosen long arm of the actual spider. -/
theorem theoremA_prescribed_zero (s n m v : Nat) (hs : 2 ≤ s) (hn : 2 ≤ n)
    (hl : 4*s-8*((s-2)/3) ≤ v) (hu : v ≤ 4*s+2*((s-2)/3)+1) (a : Fin n) :
    ∃ (hlt : v-1 < 6*s+3) (f : SpiderVertex n m (6*s+3) → Nat),
      Graceful (spiderGraph n m (6*s+3)) (n*(6*s+3)+m) f ∧
      f (.arm a ⟨v-1,hlt⟩)=0 := by
  obtain ⟨d,c,hc,hv⟩ := theoremA_cores s v hs hl hu
  have h := core_prescribed_zero (3*s) d n m v c hc hn hv a
  have hk : 2*(3*s)+3=6*s+3 := by omega
  rw [hk] at h
  exact h

/-- Theorem B: every advertised integer depth for every odd arm length 2p+3, p>=8. -/
theorem theoremB_prescribed_zero (p n m v : Nat) (hp : 8 ≤ p) (hn : 2 ≤ n)
    (hl : 8+4*((p-8)/9) ≤ v) (hu : v ≤ 9+14*((p-8)/9)) (a : Fin n) :
    ∃ (hlt : v-1 < 2*p+3) (f : SpiderVertex n m (2*p+3) → Nat),
      Graceful (spiderGraph n m (2*p+3)) (n*(2*p+3)+m) f ∧
      f (.arm a ⟨v-1,hlt⟩)=0 := by
  obtain ⟨d,c,hc,hv⟩ := theoremB_cores p v hp hl hu
  exact core_prescribed_zero p d n m v c hc hn hv a


/-- The path endpoints have the stated symmetric labels, independently of the core. -/
theorem complete_path_endpoint_labels (p : Nat) (c : List Nat) :
    (completePath p c).head?=some ((3*(2*p+3)-1)/2) ∧
    (completePath p c).getLast?=some ((3*(2*p+3)+1)/2) := by
  have h := ThirdPair.complete_path_endpoints p c
  have h1 : (3*(2*p+3)-1)/2=3*p+4 := by omega
  have h2 : (3*(2*p+3)+1)/2=3*p+5 := by omega
  simpa only [h1,h2] using h

theorem theoremA_interval_length (s : Nat) (hs : 2 ≤ s) :
    (List.range' (4*s-8*((s-2)/3))
      ((4*s+2*((s-2)/3)+1)+1-(4*s-8*((s-2)/3)))).length=10*((s-2)/3)+2 := by
  simp only [List.length_range']
  omega

theorem theoremB_interval_length (p : Nat) :
    (List.range' (8+4*((p-8)/9))
      ((9+14*((p-8)/9))+1-(8+4*((p-8)/9)))).length=10*((p-8)/9)+2 := by
  simp only [List.length_range']
  omega

/-- Explicit parameter transport to each odd arm length k>=19. -/
theorem theoremB_odd_arm_length (k n m v : Nat) (hk : 19 ≤ k) (hodd : k%2=1) (hn : 2 ≤ n)
    (hl : 8+4*((((k-3)/2)-8)/9) ≤ v) (hu : v ≤ 9+14*((((k-3)/2)-8)/9)) (a : Fin n) :
    ∃ (hlt : v-1 < k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨v-1,hlt⟩)=0 := by
  have hp : 8 ≤ (k-3)/2 := by omega
  have h := theoremB_prescribed_zero ((k-3)/2) n m v hp hn hl hu a
  have he : 2*((k-3)/2)+3=k := by omega
  rw [he] at h
  exact h

end GracefulBoundary.Variable
