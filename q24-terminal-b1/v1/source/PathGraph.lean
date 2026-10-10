import Shell
namespace GracefulBoundary

def pathGraph (M : Nat) : IndexedGraph (Fin (M+1)) (Fin M) where
  source := fun e => ⟨e.val,by omega⟩
  target := fun e => ⟨e.val+1,by omega⟩

def pathLabel (M : Nat) (c : List Nat) (v : Fin (M+1)) := c.getD v.val 0

theorem list_band_bijection (c : List Nat) (lo hi size : Nat)
    (hsize : hi+1=lo+size) (hp : c.Perm (List.range' lo size)) :
    BandBijection (fun i : Fin size => c.getD i.val 0) lo hi := by
  have hlen : c.length=size := by simpa using hp.length_eq
  have hnodup : c.Nodup := hp.nodup_iff.mpr (List.nodup_range')
  constructor
  · intro i
    have hil : i.val < c.length := by omega
    have hm : c[i.val]'hil ∈ c := List.getElem_mem hil
    have hr := hp.mem_iff.mp hm
    obtain ⟨j,hj,he⟩ := List.mem_range'.mp hr
    rw [← List.getElem_eq_getD (h:=hil) 0]
    constructor <;> omega
  · intro i j he
    have hi : i.val < c.length := by omega
    have hj : j.val < c.length := by omega
    have hij := (hnodup.getD_inj hi hj).mp he
    exact Fin.ext hij
  · intro x hx ht
    have hm : x ∈ List.range' lo size := List.mem_range'.mpr ⟨x-lo,by omega,by omega⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (hp.mem_iff.mpr hm)
    refine ⟨⟨i,by omega⟩,?_⟩
    rw [← List.getElem_eq_getD (h:=hi) 0]
    exact he

theorem edgeDiffs_lookup (c : List Nat) (i : Nat) (hi : i+1 < c.length) :
    (edgeDiffs c).getD i 0=distance (c.getD i 0) (c.getD (i+1) 0) := by
  induction c using edgeDiffs.induct generalizing i with
  | case1 => simp at hi
  | case2 a => simp at hi
  | case3 a b xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have ht : i+1 < (b::xs).length := by simp at hi ⊢; omega
      simpa only [edgeDiffs,List.getD_cons_succ] using ih i ht

theorem crosses_lookup (A : Nat) (c : List Nat) (hc : crosses A c)
    (i : Nat) (hi : i+1 < c.length) : cross A (c.getD i 0) (c.getD (i+1) 0) := by
  induction c using crosses.induct generalizing i with
  | case1 => simp at hi
  | case2 a => simp at hi
  | case3 a b xs ih =>
    cases i with
    | zero => exact hc.1
    | succ i =>
      have ht : i+1 < (b::xs).length := by simp at hi ⊢; omega
      simpa only [List.getD_cons_succ] using ih hc.2 i ht

theorem list_path_graceful (M : Nat) (c : List Nat)
    (hv : c.Perm (List.range (M+1)))
    (he : (edgeDiffs c).Perm (List.range' 1 M)) :
    Graceful (pathGraph M) M (pathLabel M c) := by
  have hlen : c.length=M+1 := by simpa using hv.length_eq
  constructor
  · exact list_band_bijection c 0 M (M+1) (by omega) (by simpa [List.range_eq_range'] using hv)
  · have hb := list_band_bijection (edgeDiffs c) 1 M M (by omega) he
    have hfun : (fun i : Fin M => (edgeDiffs c).getD i.val 0)=weight (pathGraph M) (pathLabel M c) := by
      funext i
      exact edgeDiffs_lookup c i.val (by omega)
    rw [hfun] at hb
    exact hb

theorem list_path_alpha (M A : Nat) (c : List Nat) (hlen : c.length=M+1)
    (hc : crosses A c) : Alpha (pathGraph M) A (pathLabel M c) := by
  intro e
  exact crosses_lookup A c hc e.val (by omega)

/-- Full indexed graph interpretation of each prescribed-depth certificate. -/
theorem certificate_graph (s : Nat) (c : List Nat) (hc : PathCertificate s c) :
    Graceful (pathGraph (12*s+6)) (12*s+6) (pathLabel (12*s+6) c) ∧
    Alpha (pathGraph (12*s+6)) (6*s+2) (pathLabel (12*s+6) c) := by
  rcases hc with ⟨hlen,hv,he,ha,_⟩
  exact ⟨list_path_graceful (12*s+6) c hv he,list_path_alpha (12*s+6) (6*s+2) c hlen ha⟩

/-- Distinguished midpoint and anchors in the actual indexed graph. -/
theorem certificate_graph_anchors (s : Nat) (c : List Nat) (hc : PathCertificate s c) :
    pathLabel (12*s+6) c ⟨6*s+3,by omega⟩=6*s+2 ∧
    pathLabel (12*s+6) c ⟨2*s+3,by omega⟩=0 ∧
    pathLabel (12*s+6) c ⟨2*s+2,by omega⟩=12*s+6 := by
  rcases hc with ⟨_,_,_,_,hm,hz,hx⟩
  simp [pathLabel,List.getD_eq_getElem?_getD,hm,hz,hx]

end GracefulBoundary

