import ThirdRecurrence
namespace GracefulBoundary.ThirdPair

def PathCertificate (s : Nat) (c : List Nat) : Prop :=
  c.length=12*s+7 ∧ c.Perm (List.range (12*s+7)) ∧
  (edgeDiffs c).Perm (List.range' 1 (12*s+6)) ∧ crosses (6*s+2) c ∧
  c[6*s+3]?=some (6*s+2) ∧ c[2*s-1]?=some 0 ∧ c[2*s-2]?=some (12*s+6) ∧
  c[0]?=some (9*s+4) ∧ c[12*s+6]?=some (9*s+5)

def direct2 : List Nat :=
  [22,3,30,0,29,1,24,6,26,5,27,2,28,4,17,14,15,13,18,11,21,7,19,10,16,12,20,9,25,8,23]

theorem direct2_valid : PathCertificate 2 direct2 := by unfold PathCertificate; decide

theorem complete_path_endpoints (p : Nat) (c : List Nat) :
    (completePath p c).head?=some (3*p+4) ∧ (completePath p c).getLast?=some (3*p+5) := by
  constructor
  · simp [completePath]
  · unfold completePath
    rw [List.getLast?_append]
    rfl

theorem core_to_path_bridge (s : Nat) (c : List Nat) (hs : 3 ≤ s) (hc : AnchoredCore s c) :
    PathCertificate s (completePath (3*s) c) := by
  have hgeneric := boundary_shell_bridge (3*s) c hc.1
  have hlen := hc.1.2.1
  have hz := complete_path_core_lookup (3*s) c (4*s+3) hlen (by omega)
  have hm := complete_path_core_lookup (3*s) c (4*s+4) hlen (by omega)
  rw [coreLabels_lookup,hc.2.1] at hz
  rw [coreLabels_lookup,hc.2.2] at hm
  have e1 : 2*(3*s)+2-(4*s+3)=2*s-1 := by omega
  have e2 : 2*(3*s)+2-(4*s+4)=2*s-2 := by omega
  have hodd : ¬ (4*s+3)%2=0 := by omega
  have heven : (4*s+4)%2=0 := by omega
  simp only [e1,hodd,ite_false,Option.map_some] at hz
  simp only [e2,heven,ite_true,Option.map_some,Nat.sub_zero] at hm
  rcases hgeneric with ⟨hl,hv,he,ha,hmid⟩
  have h12 : 4*(3*s)=12*s := by omega
  have h6 : 2*(3*s)=6*s := by omega
  have hend := complete_path_endpoints (3*s) c
  rw [List.head?_eq_getElem?] at hend
  rw [List.getLast?_eq_getElem?,hl] at hend
  refine ⟨by simpa only [h12] using hl,by simpa only [h12] using hv,
    by simpa only [h12] using he,by simpa only [h6] using ha,
    by simpa only [h6] using hmid,hz,by simpa only [h12] using hm,?_,?_⟩
  · simpa only [show 3*(3*s)=9*s by omega] using hend.1
  · simpa only [show 4*(3*s)+7-1=12*s+6 by omega,show 3*(3*s)=9*s by omega] using hend.2

theorem uniform_midpoint_alpha_paths : ∀ s,2 ≤ s → ∃ c,PathCertificate s c := by
  intro s hs
  by_cases h2 : s=2
  · subst s; exact ⟨direct2,direct2_valid⟩
  obtain ⟨c,hc⟩ := uniform_anchored_cores s (by omega)
  exact ⟨completePath (3*s) c,core_to_path_bridge s c (by omega) hc⟩

theorem certificate_graph (s : Nat) (c : List Nat) (hc : PathCertificate s c) :
    Graceful (pathGraph (12*s+6)) (12*s+6) (pathLabel (12*s+6) c) ∧
    Alpha (pathGraph (12*s+6)) (6*s+2) (pathLabel (12*s+6) c) := by
  rcases hc with ⟨hlen,hv,he,ha,_⟩
  exact ⟨list_path_graceful (12*s+6) c hv he,list_path_alpha (12*s+6) (6*s+2) c hlen ha⟩

theorem certificate_graph_anchors (s : Nat) (c : List Nat) (hc : PathCertificate s c) :
    pathLabel (12*s+6) c ⟨6*s+3,by omega⟩=6*s+2 ∧
    pathLabel (12*s+6) c ⟨2*s-1,by omega⟩=0 ∧
    pathLabel (12*s+6) c ⟨2*s-2,by omega⟩=12*s+6 := by
  rcases hc with ⟨_,_,_,_,hm,hz,hx,_,_⟩
  simp [pathLabel,List.getD_eq_getElem?_getD,hm,hz,hx]

theorem certificate_graph_endpoints (s : Nat) (c : List Nat) (hc : PathCertificate s c) :
    pathLabel (12*s+6) c ⟨0,by omega⟩=(3*(6*s+3)-1)/2 ∧
    pathLabel (12*s+6) c ⟨12*s+6,by omega⟩=(3*(6*s+3)+1)/2 := by
  rcases hc with ⟨_,_,_,_,_,_,_,hf,hl⟩
  simp only [pathLabel,List.getD_eq_getElem?_getD,hf,hl,Option.getD_some]
  omega

end GracefulBoundary.ThirdPair

