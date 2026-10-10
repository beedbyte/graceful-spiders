import GapWeights
namespace GracefulBoundary.FixedEven

def CertifiedLength (k : Nat) : Prop := k=6 ∨ k=8 ∨ k=10 ∨ k=12 ∨ k=14 ∨ k=16
def BaseCertificate (k : Nat) (c : List Nat) : Prop :=
  6≤k ∧ k%2=0 ∧ c.length=2*k+1 ∧ c.Perm (List.range (2*k+1)) ∧
  (edgeDiffs c).Perm (List.range' 1 (2*k)) ∧ crosses k c ∧
  c[k]?=some 1 ∧ c[k+1]?=some (2*k) ∧ c[k+2]?=some 0

def seed6 := [4,8,5,7,6,11,1,12,0,9,3,10,2]
def seed8 := [5,9,8,10,7,15,2,13,1,16,0,14,4,11,6,12,3]
def seed10 := [7,12,10,11,8,15,9,13,5,14,1,20,0,18,2,19,4,16,6,17,3]
def seed12 := [3,20,6,19,7,18,8,17,2,22,4,23,1,24,0,21,5,13,12,14,11,15,10,16,9]
def seed14 := [8,24,4,27,2,23,5,17,13,18,11,22,3,25,1,28,0,26,9,19,10,16,14,15,12,20,7,21,6]
def seed16 := [10,20,9,22,5,28,4,24,8,26,7,29,3,30,2,31,1,32,0,25,11,23,14,18,13,21,15,17,16,19,12,27,6]

theorem seed6_valid : BaseCertificate 6 seed6 := by unfold BaseCertificate; decide
theorem seed8_valid : BaseCertificate 8 seed8 := by unfold BaseCertificate; decide
theorem seed10_valid : BaseCertificate 10 seed10 := by unfold BaseCertificate; decide
theorem seed12_valid : BaseCertificate 12 seed12 := by unfold BaseCertificate; decide
theorem seed14_valid : BaseCertificate 14 seed14 := by unfold BaseCertificate; decide
theorem seed16_valid : BaseCertificate 16 seed16 := by unfold BaseCertificate; decide

theorem certified_bases (k : Nat) (hk : CertifiedLength k) : ∃c,BaseCertificate k c := by
  rcases hk with h|h|h|h|h|h <;> subst k
  · exact ⟨seed6,seed6_valid⟩
  · exact ⟨seed8,seed8_valid⟩
  · exact ⟨seed10,seed10_valid⟩
  · exact ⟨seed12,seed12_valid⟩
  · exact ⟨seed14,seed14_valid⟩
  · exact ⟨seed16,seed16_valid⟩

/-- Actual alpha-labeled path seeds, with all three pins, only at six certified lengths. -/
theorem certified_alpha_paths (k : Nat) (hk : CertifiedLength k) :
    ∃ (hlt : k+2<2*k+1) (f : Fin (2*k+1) → Nat), Graceful (pathGraph (2*k)) (2*k) f ∧
      Alpha (pathGraph (2*k)) k f ∧ f ⟨k,by omega⟩=1 ∧ f ⟨k+1,by omega⟩=2*k ∧ f ⟨k+2,hlt⟩=0 := by
  obtain ⟨c,hc⟩ := certified_bases k hk
  rcases hc with ⟨lower,_,len,hv,he,ha,h1,hmax,hzero⟩
  refine ⟨by omega,pathLabel (2*k) c,list_path_graceful (2*k) c hv he,list_path_alpha (2*k) k c len ha,?_,?_,?_⟩
  · simp [pathLabel,List.getD_eq_getElem?_getD,h1]
  · simp [pathLabel,List.getD_eq_getElem?_getD,hmax]
  · simp [pathLabel,List.getD_eq_getElem?_getD,hzero]

end GracefulBoundary.FixedEven
