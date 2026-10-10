import PinnedPath
namespace GracefulBoundary.CenterLeaves

def graph (k m : Nat) : IndexedGraph (Sum (Fin (2*k+1)) (Fin m)) (Sum (Fin (2*k)) (Fin m)) where
  source := fun e => match e with
    | .inl e => .inl ⟨e.val,by omega⟩
    | .inr _ => .inl ⟨k,by omega⟩
  target := fun e => match e with
    | .inl e => .inl ⟨e.val+1,by omega⟩
    | .inr j => .inr j

theorem lifted_old_label (k m : Nat) (hk : 2≤k) (g : Fin (2*k+1) → Nat)
    (hg : Graceful (pathGraph (2*k)) (2*k) g) (hmax : g ⟨k+1,by omega⟩=2*k) (v : Fin (2*k+1)) :
    insertLabel g (2*k) m (.inl v)=if v.val=k+1 then 2*k+m else g v := by
  dsimp only [insertLabel]
  by_cases he : v.val=k+1
  · have hv : v=⟨k+1,by omega⟩ := Fin.ext he
    rw [hv,hmax,ite_eq_left (by omega),ite_eq_left (by omega)]
  · have bound := (hg.vertices.bounds v).2
    have neq : g v≠2*k := by
      intro h; have hv := hg.vertices.injective v ⟨k+1,by omega⟩ (h.trans hmax.symm)
      have := congrArg Fin.val hv; exact he this
    rw [ite_eq_right (by omega),ite_eq_right he]

theorem pinned_weight (k : Nat) (hk : 2≤k) (g : Fin (2*k+1) → Nat)
    (hroot : g ⟨k,by omega⟩=1) (hmax : g ⟨k+1,by omega⟩=2*k)
    (hzero : g ⟨k+2,by omega⟩=0) :
    weight (pathGraph (2*k)) g ⟨k,by omega⟩=2*k-1 ∧
    weight (pathGraph (2*k)) g ⟨k+1,by omega⟩=2*k := by
  dsimp only [weight,pathGraph]
  rw [hroot,hmax,hzero]
  dsimp only [distance]
  constructor <;> omega

theorem lifted_old_weight (k m : Nat) (hk : 2≤k) (g : Fin (2*k+1) → Nat)
    (hg : Graceful (pathGraph (2*k)) (2*k) g)
    (hroot : g ⟨k,by omega⟩=1) (hmax : g ⟨k+1,by omega⟩=2*k)
    (hzero : g ⟨k+2,by omega⟩=0) (e : Fin (2*k)) :
    weight (graph k m) (insertLabel g (2*k) m) (.inl e)=
      insertLabel (weight (pathGraph (2*k)) g) (2*k-1) m (.inl e) := by
  have pins := pinned_weight k hk g hroot hmax hzero
  by_cases he : e.val=k
  · have ee : e=⟨k,by omega⟩ := Fin.ext he
    rw [ee]
    dsimp only [weight,graph]
    rw [lifted_old_label k m hk g hg hmax,lifted_old_label k m hk g hg hmax]
    dsimp only
    simp only [show k≠k+1 by omega,ite_false,ite_true,hroot,insertLabel,pins.1,Nat.le_refl]
    dsimp only [distance]
    omega
  · by_cases he1 : e.val=k+1
    · have ee : e=⟨k+1,by omega⟩ := Fin.ext he1
      rw [ee]
      dsimp only [weight,graph]
      rw [lifted_old_label k m hk g hg hmax,lifted_old_label k m hk g hg hmax]
      dsimp only
      simp only [show k+1+1≠k+1 by omega,ite_false,ite_true,hzero,insertLabel,pins.2]
      rw [ite_eq_left (by omega)]
      dsimp only [distance]
      omega
    · have small : weight (pathGraph (2*k)) g e<2*k-1 := by
        have bound := (hg.edges.bounds e).2
        have neq0 : weight (pathGraph (2*k)) g e≠2*k-1 := by
          intro h; have hv := hg.edges.injective e ⟨k,by omega⟩ (h.trans pins.1.symm)
          have := congrArg Fin.val hv; exact he this
        have neq1 : weight (pathGraph (2*k)) g e≠2*k := by
          intro h; have hv := hg.edges.injective e ⟨k+1,by omega⟩ (h.trans pins.2.symm)
          have := congrArg Fin.val hv; exact he1 this
        omega
      dsimp only [weight,graph]
      rw [lifted_old_label k m hk g hg hmax,lifted_old_label k m hk g hg hmax]
      dsimp only
      rw [ite_eq_right he1,ite_eq_right (by omega)]
      change weight (pathGraph (2*k)) g e=insertLabel (weight (pathGraph (2*k)) g) (2*k-1) m (.inl e)
      dsimp only [insertLabel]
      rw [ite_eq_right (by omega)]

theorem lifted_leaf_weight (k m : Nat) (hk : 2≤k) (g : Fin (2*k+1) → Nat)
    (hg : Graceful (pathGraph (2*k)) (2*k) g) (hroot : g ⟨k,by omega⟩=1)
    (hmax : g ⟨k+1,by omega⟩=2*k) (j : Fin m) :
    weight (graph k m) (insertLabel g (2*k) m) (.inr j)=2*k-1+j.val := by
  dsimp only [weight,graph]
  rw [lifted_old_label k m hk g hg hmax]
  dsimp only
  rw [ite_eq_right (by omega),hroot]
  dsimp only [insertLabel,distance]
  omega

/-- Conditional maximum lift on an actual path with named center leaves. -/
theorem pinned_path_leaf_extension (k m : Nat) (hk : 2≤k) (g : Fin (2*k+1) → Nat)
    (hg : Graceful (pathGraph (2*k)) (2*k) g)
    (hroot : g ⟨k,by omega⟩=1) (hmax : g ⟨k+1,by omega⟩=2*k)
    (hzero : g ⟨k+2,by omega⟩=0) :
    Graceful (graph k m) (2*k+m) (insertLabel g (2*k) m) ∧
      insertLabel g (2*k) m (.inl ⟨k,by omega⟩)=1 := by
  constructor
  · constructor
    · exact band_insert g 0 (2*k) (2*k) m hg.vertices (by omega)
    · have hb := band_insert (weight (pathGraph (2*k)) g) 1 (2*k) (2*k-1) m hg.edges (by omega)
      have he : weight (graph k m) (insertLabel g (2*k) m)=insertLabel (weight (pathGraph (2*k)) g) (2*k-1) m := by
        funext e; cases e with
        | inl e => exact lifted_old_weight k m hk g hg hroot hmax hzero e
        | inr j => exact lifted_leaf_weight k m hk g hg hroot hmax j
      rw [he]; exact hb
  · rw [lifted_old_label k m hk g hg hmax]
    dsimp only
    rw [ite_eq_right (by omega),hroot]

theorem center_one_path_leaves (k m : Nat) (hk : 7≤k) :
    ∃ f : Sum (Fin (2*k+1)) (Fin m) → Nat,
      Graceful (graph k m) (2*k+m) f ∧ f (.inl ⟨k,by omega⟩)=1 := by
  obtain ⟨g,hg,hr,hm,hz⟩ := midpoint_pinned_graceful_path k hk
  exact ⟨insertLabel g (2*k) m,pinned_path_leaf_extension k m (by omega) g hg hr hm hz⟩

end GracefulBoundary.CenterLeaves
