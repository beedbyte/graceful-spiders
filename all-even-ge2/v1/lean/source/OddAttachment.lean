import OddPacket
import PathGraph

namespace GracefulBoundary.OddNearTip

def graph {W E : Type} (H : IndexedGraph W E) (root : W) (r : Nat) :
    IndexedGraph (Sum W (Fin (2*r+1))) (Sum E (Fin (2*r+1))) where
  source := fun e => match e with
    | .inl e => .inl (H.source e)
    | .inr d => if d.val=0 then .inl root else .inr ⟨d.val-1,by omega⟩
  target := fun e => match e with
    | .inl e => .inl (H.target e)
    | .inr d => .inr d

def label {W : Type} (Q r : Nat) (c : List Nat) (g : W → Nat) : Sum W (Fin (2*r+1)) → Nat
  | .inl w => r+1+g w
  | .inr d => (armLabels Q r c).getD d.val 0

theorem arm_bounds (Q r : Nat) (c : List Nat) (hc : Packet r c) (d : Fin (2*r+1)) :
    (armLabels Q r c).getD d.val 0<r+1 ∨
      (Q+r+2≤(armLabels Q r c).getD d.val 0 ∧ (armLabels Q r c).getD d.val 0≤Q+2*r+1) := by
  have index : d.val<(armLabels Q r c).length := by rw [arm_length Q r c hc]; exact d.isLt
  have mem : (armLabels Q r c).getD d.val 0∈armLabels Q r c := by
    rw [←List.getElem_eq_getD (h:=index) 0]
    exact List.getElem_mem index
  have bands := (arm_permutation Q r c hc).mem_iff.mp mem
  simp only [List.mem_append,List.mem_range,List.mem_range'_1] at bands
  omega

theorem arm_nodup (Q r : Nat) (c : List Nat) (hc : Packet r c) : (armLabels Q r c).Nodup := by
  apply (arm_permutation Q r c hc).nodup_iff.mpr
  rw [List.nodup_append]
  refine ⟨List.nodup_range,List.nodup_range',?_⟩
  intro x hx y hy he
  subst y
  simp only [List.mem_range] at hx
  simp only [List.mem_range'_1] at hy
  omega

theorem arm_onto (Q r x : Nat) (c : List Nat) (hc : Packet r c)
    (hx : x<r+1 ∨ (Q+r+2≤x ∧ x≤Q+2*r+1)) :
    ∃ d : Fin (2*r+1),(armLabels Q r c).getD d.val 0=x := by
  have mem : x∈List.range (r+1)++List.range' (Q+r+2) r := by
    simp only [List.mem_append,List.mem_range,List.mem_range'_1]
    omega
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp ((arm_permutation Q r c hc).mem_iff.mpr mem)
  refine ⟨⟨i,by rw [←arm_length Q r c hc]; exact hi⟩,?_⟩
  rw [←List.getElem_eq_getD (h:=hi) 0]
  exact he

theorem vertex_band (Q r : Nat) (c : List Nat) (hc : Packet r c) {W : Type} (g : W → Nat)
    (hg : BandBijection g 0 Q) : BandBijection (label Q r c g) 0 (Q+2*r+1) := by
  constructor
  · intro v
    cases v with
    | inl w => have hb := hg.bounds w; dsimp only [label]; omega
    | inr d => have hb := arm_bounds Q r c hc d; dsimp only [label]; omega
  · intro v w he
    cases v with
    | inl v =>
      cases w with
      | inl w =>
        have eq : g v=g w := by dsimp only [label] at he; omega
        exact congrArg Sum.inl (hg.injective v w eq)
      | inr d =>
        have old := hg.bounds v
        have new := arm_bounds Q r c hc d
        dsimp only [label] at he
        omega
    | inr d =>
      cases w with
      | inl w =>
        have old := hg.bounds w
        have new := arm_bounds Q r c hc d
        dsimp only [label] at he
        omega
      | inr e =>
        have hd : d.val<(armLabels Q r c).length := by rw [arm_length Q r c hc]; exact d.isLt
        have hee : e.val<(armLabels Q r c).length := by rw [arm_length Q r c hc]; exact e.isLt
        have eq := ((arm_nodup Q r c hc).getD_inj hd hee).mp he
        exact congrArg Sum.inr (Fin.ext eq)
  · intro x _ hx
    by_cases low : x<r+1
    · obtain ⟨d,hd⟩ := arm_onto Q r x c hc (Or.inl low)
      exact ⟨.inr d,hd⟩
    by_cases high : Q+r+1<x
    · obtain ⟨d,hd⟩ := arm_onto Q r x c hc (Or.inr (by omega))
      exact ⟨.inr d,hd⟩
    · obtain ⟨w,hw⟩ := hg.onto (x-(r+1)) (by omega) (by omega)
      refine ⟨.inl w,?_⟩
      dsimp only [label]
      omega

theorem old_weight {W E : Type} (H : IndexedGraph W E) (root : W) (Q r : Nat)
    (c : List Nat) (g : W → Nat) (e : E) :
    weight (graph H root r) (label Q r c g) (.inl e)=weight H g e := by
  dsimp only [weight,graph,label]
  exact translate_difference (r+1) _ _

theorem new_weight {W E : Type} (H : IndexedGraph W E) (root : W) (Q r : Nat)
    (c : List Nat) (hc : Packet r c) (g : W → Nat) (hQ : 1≤Q) (hroot : g root=Q-1) (d : Fin (2*r+1)) :
    weight (graph H root r) (label Q r c g) (.inr d)=
      (edgeDiffs (decode (Q+2*r+1) true c)).getD d.val 0 := by
  have index : d.val+1<(decode (Q+2*r+1) true c).length := by rw [LabelOne.decode_length,hc.length]; have := d.isLt; omega
  rw [edgeDiffs_lookup _ _ index,decoded_first Q r c hc]
  by_cases zero : d.val=0
  · dsimp only [weight,graph]
    have rootEq : r+1+g root=Q+r := by rw [hroot]; omega
    simp only [zero,ite_true,label,List.getD_cons_zero,List.getD_cons_succ]
    rw [rootEq]
  · obtain ⟨j,eq⟩ : ∃ j,d.val=j+1 := ⟨d.val-1,by omega⟩
    dsimp only [weight,graph]
    simp [eq,label]

theorem edge_band {W E : Type} (H : IndexedGraph W E) (root : W) (Q r : Nat)
    (c : List Nat) (hc : Packet r c) (g : W → Nat) (hg : Graceful H Q g) (hQ : 1≤Q) (hroot : g root=Q-1) :
    BandBijection (weight (graph H root r) (label Q r c g)) 1 (Q+2*r+1) := by
  have new := list_band_bijection (edgeDiffs (decode (Q+2*r+1) true c)) (Q+1) (Q+2*r+1) (2*r+1)
    (by omega) (arm_differences Q r c hc)
  constructor
  · intro e
    cases e with
    | inl e => rw [old_weight]; have hb := hg.edges.bounds e; omega
    | inr d => rw [new_weight H root Q r c hc g hQ hroot]; have hb := new.bounds d; omega
  · intro e f he
    cases e with
    | inl e =>
      cases f with
      | inl f => rw [old_weight,old_weight] at he; exact congrArg Sum.inl (hg.edges.injective e f he)
      | inr d =>
        rw [old_weight,new_weight H root Q r c hc g hQ hroot] at he
        have old := hg.edges.bounds e
        have hb := new.bounds d
        omega
    | inr d =>
      cases f with
      | inl e =>
        rw [old_weight,new_weight H root Q r c hc g hQ hroot] at he
        have old := hg.edges.bounds e
        have hb := new.bounds d
        omega
      | inr f =>
        rw [new_weight H root Q r c hc g hQ hroot,new_weight H root Q r c hc g hQ hroot] at he
        exact congrArg Sum.inr (new.injective d f he)
  · intro x hlo hhi
    by_cases old : x≤Q
    · obtain ⟨e,he⟩ := hg.edges.onto x hlo old
      exact ⟨.inl e,by rw [old_weight]; exact he⟩
    · obtain ⟨d,hd⟩ := new.onto x (by omega) hhi
      exact ⟨.inr d,by rw [new_weight H root Q r c hc g hQ hroot]; exact hd⟩

theorem packet_attachment_graceful {W E : Type} (H : IndexedGraph W E) (root : W)
    (Q r : Nat) (c : List Nat) (hc : Packet r c) (g : W → Nat)
    (hg : Graceful H Q g) (hQ : 1≤Q) (hroot : g root=Q-1) :
    Graceful (graph H root r) (Q+2*r+1) (label Q r c g) :=
  ⟨vertex_band Q r c hc g hg.vertices,edge_band H root Q r c hc g hg hQ hroot⟩

theorem odd_root_last_attachment {W E : Type} (H : IndexedGraph W E) (root : W)
    (Q r : Nat) (hr : 3≤r) (g : W → Nat) (hg : Graceful H Q g) (hQ : 1≤Q) (hroot : g root=Q-1) :
    ∃ f : Sum W (Fin (2*r+1)) → Nat,
      Graceful (graph H root r) (Q+2*r+1) f ∧ f (.inr ⟨2*r+1-3,by omega⟩)=0 := by
  obtain ⟨c,hc⟩ := packets r hr
  refine ⟨label Q r c g,packet_attachment_graceful H root Q r c hc g hg hQ hroot,?_⟩
  have zero := hc.decodedZero (Q+2*r+1)
  rw [decoded_first Q r c hc] at zero
  have index : 2*r-1=(2*r+1-3)+1 := by omega
  rw [index,List.getElem?_cons_succ] at zero
  dsimp only [label]
  rw [List.getD_eq_getElem?_getD,zero]
  rfl

end GracefulBoundary.OddNearTip
