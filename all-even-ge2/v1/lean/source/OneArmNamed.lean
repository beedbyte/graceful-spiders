import OneArmAlpha
namespace GracefulBoundary.EvenBoundary.Single
open FixedEven

def toV (k m : Nat) : SpiderVertex 1 m k → Sum (Fin (k+1)) (Fin m)
  | .center => .inl ⟨0,by omega⟩
  | .leaf j => .inr j
  | .arm _ d => .inl ⟨d.val+1,by omega⟩
def fromV (k m : Nat) : Sum (Fin (k+1)) (Fin m) → SpiderVertex 1 m k
  | .inr j => .leaf j
  | .inl v => if hv : v.val=0 then .center else .arm ⟨0,by omega⟩ ⟨v.val-1,by omega⟩
def toE (k m : Nat) : SpiderEdge 1 m k → Sum (Fin k) (Fin m)
  | .leaf j => .inr j
  | .arm _ d => .inl d
def fromE (k m : Nat) : Sum (Fin k) (Fin m) → SpiderEdge 1 m k
  | .inr j => .leaf j
  | .inl e => .arm ⟨0,by omega⟩ e

theorem vertex_left_inverse (k m : Nat) (v : SpiderVertex 1 m k) : fromV k m (toV k m v)=v := by
  cases v with
  | center => simp only [toV,fromV,dite_true]
  | leaf j => rfl
  | arm i d =>
    dsimp only [toV,fromV]
    rw [dite_eq_right (by omega)]
    congr 1 <;> apply Fin.ext <;> dsimp only <;> omega
theorem vertex_right_inverse (k m : Nat) (v : Sum (Fin (k+1)) (Fin m)) : toV k m (fromV k m v)=v := by
  cases v with
  | inr j => rfl
  | inl v =>
    dsimp only [fromV]; split <;> dsimp only [toV] <;> congr 1 <;> apply Fin.ext <;> dsimp only <;> omega
theorem edge_left_inverse (k m : Nat) (e : SpiderEdge 1 m k) : fromE k m (toE k m e)=e := by
  cases e with
  | leaf j => rfl
  | arm i d => dsimp only [toE,fromE]; congr 1; apply Fin.ext; dsimp only; omega
theorem edge_right_inverse (k m : Nat) (e : Sum (Fin k) (Fin m)) : toE k m (fromE k m e)=e := by cases e <;> rfl

theorem source_eq (k m : Nat) (e : SpiderEdge 1 m k) :
    toV k m ((spiderGraph 1 m k).source e)=
      (leavesGraph (pathGraph k) ⟨0,by omega⟩ m).source (toE k m e) := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    by_cases hd : d.val=0 <;> simp only [spiderGraph,toV,toE,leavesGraph,pathGraph,hd,ite_true,ite_false]
    all_goals congr 1; apply Fin.ext; dsimp only; omega
theorem target_eq (k m : Nat) (e : SpiderEdge 1 m k) :
    toV k m ((spiderGraph 1 m k).target e)=
      (leavesGraph (pathGraph k) ⟨0,by omega⟩ m).target (toE k m e) := by cases e <;> rfl
theorem weights (k m : Nat) (f : Sum (Fin (k+1)) (Fin m) → Nat) (e : SpiderEdge 1 m k) :
    weight (spiderGraph 1 m k) (fun v => f (toV k m v)) e=
      weight (leavesGraph (pathGraph k) ⟨0,by omega⟩ m) f (toE k m e) := by
  dsimp only [weight]; rw [source_eq,target_eq]
theorem graceful_actual (k m q : Nat) (f : Sum (Fin (k+1)) (Fin m) → Nat)
    (hf : Graceful (leavesGraph (pathGraph k) ⟨0,by omega⟩ m) q f) :
    Graceful (spiderGraph 1 m k) q (fun v => f (toV k m v)) := by
  constructor
  · exact NearTip.band_transport f 0 q hf.vertices (toV k m) (fromV k m) (vertex_left_inverse k m) (vertex_right_inverse k m)
  · have hb := NearTip.band_transport (weight (leavesGraph (pathGraph k) ⟨0,by omega⟩ m) f) 1 q hf.edges (toE k m) (fromE k m) (edge_left_inverse k m) (edge_right_inverse k m)
    rw [funext (weights k m f)]; exact hb

theorem path_maximum_anchor (k : Nat) (hk : 2≤k) :
    MaximumAnchor (pathGraph k) ⟨0,by omega⟩ ⟨1,by omega⟩ ⟨2,by omega⟩ ⟨0,by omega⟩ ⟨1,by omega⟩ := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · intro e
    by_cases h0 : e.val=0
    · left; exact Fin.ext h0
    · by_cases h1 : e.val=1
      · right; left; exact Fin.ext h1
      · right; right; constructor
        · intro he; have hv := congrArg Fin.val he; dsimp only [pathGraph] at hv; omega
        · intro he; have hv := congrArg Fin.val he; dsimp only [pathGraph] at hv; omega

theorem pinned_one_arm_leaf_extension (k m : Nat) (hk : 2≤k) (g : Fin (k+1) → Nat)
    (hg : Graceful (pathGraph k) k g) (hr : g ⟨0,by omega⟩=1) (hm : g ⟨1,by omega⟩=k) (hz : g ⟨2,by omega⟩=0) :
    ∃ f : SpiderVertex 1 m k → Nat, Graceful (spiderGraph 1 m k) (k+m) f ∧ f .center=1 := by
  have hf := maximum_leaf_extension (pathGraph k) k m g hg ⟨0,by omega⟩ ⟨1,by omega⟩ ⟨2,by omega⟩ ⟨0,by omega⟩ ⟨1,by omega⟩ (path_maximum_anchor k hk) hr hm hz hk
  exact ⟨fun v => CenterLeaves.insertLabel g k m (toV k m v),graceful_actual k m (k+m) _ hf.1,hf.2⟩

theorem all_one_arm_center_one (r m : Nat) (hr : 3≤r) :
    ∃ f : SpiderVertex 1 m (2*r) → Nat, Graceful (spiderGraph 1 m (2*r)) (2*r+m) f ∧ f .center=1 := by
  obtain ⟨g,hg,_,hroot,hmax,hzero⟩ := one_arm_anchored_alpha r hr
  exact pinned_one_arm_leaf_extension (2*r) m (by omega) g hg hroot hmax hzero

end GracefulBoundary.EvenBoundary.Single
