import PathGraph
namespace GracefulBoundary

abbrev Rectangle (h k : Nat) := Fin h × Fin k

def flatLabel (h k : Nat) (x : Rectangle h k) := x.1.val*k+x.2.val+1

theorem rectangle_band (h k : Nat) (hk : 0 < k) :
    BandBijection (flatLabel h k) 1 (h*k) := by
  constructor
  · intro x
    have hi := Nat.mul_le_mul_right k (show x.1.val+1 ≤ h by omega)
    simp only [Nat.add_mul,Nat.one_mul] at hi
    unfold flatLabel
    constructor <;> omega
  · intro x y he
    have hsum : x.1.val*k+x.2.val=y.1.val*k+y.2.val := by unfold flatLabel at he; omega
    have hmod := congrArg (fun t => t%k) hsum
    simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt x.2.isLt,Nat.mod_eq_of_lt y.2.isLt] at hmod
    have hprod : x.1.val*k=y.1.val*k := by omega
    have hi := Nat.eq_of_mul_eq_mul_right hk hprod
    exact Prod.ext (Fin.ext hi) (Fin.ext hmod)
  · intro x hx htop
    have hi : (x-1)/k < h := (Nat.div_lt_iff_lt_mul hk).mpr (by omega)
    have hj : (x-1)%k < k := Nat.mod_lt _ hk
    refine ⟨⟨⟨(x-1)/k,hi⟩,⟨(x-1)%k,hj⟩⟩,?_⟩
    have hd := Nat.div_add_mod (x-1) k
    simp only [flatLabel]
    rw [Nat.mul_comm]
    omega

theorem band_precompose {V W : Type} (f : V → Nat) (lo hi : Nat)
    (hf : BandBijection f lo hi) (g : W → V) (inv : V → W)
    (hleft : ∀ w, inv (g w)=w) (hright : ∀ v, g (inv v)=v) :
    BandBijection (fun w => f (g w)) lo hi := by
  constructor
  · intro w; exact hf.bounds _
  · intro w z he
    have hg := hf.injective _ _ he
    have h := congrArg inv hg
    simpa only [hleft] using h
  · intro x hx ht
    obtain ⟨v,hv⟩ := hf.onto x hx ht
    exact ⟨inv v,by rw [hright,hv]⟩

def mirror (h : Nat) (i : Fin h) : Fin h := ⟨h-1-i.val,by omega⟩

theorem mirror_mirror (h : Nat) (i : Fin h) : mirror h (mirror h i)=i := by
  apply Fin.ext
  simp only [mirror]
  omega

def vertexCode (h r : Nat) (x : Rectangle h (2*r+1)) : Rectangle h (2*r+1) :=
  if x.2.val%2=0 then (mirror h x.1,⟨2*r-x.2.val/2,by omega⟩)
  else (x.1,⟨x.2.val/2,by omega⟩)

def vertexDecode (h r : Nat) (x : Rectangle h (2*r+1)) : Rectangle h (2*r+1) :=
  if hlt : x.2.val<r then (x.1,⟨2*x.2.val+1,by omega⟩)
  else (mirror h x.1,⟨2*(2*r-x.2.val),by omega⟩)

theorem vertexDecode_code (h r : Nat) (x : Rectangle h (2*r+1)) :
    vertexDecode h r (vertexCode h r x)=x := by
  unfold vertexCode
  split
  · rename_i he
    have hge : ¬ 2*r-x.2.val/2 < r := by omega
    simp only [vertexDecode,dite_eq_right hge,mirror_mirror]
    apply Prod.ext
    · rfl
    · apply Fin.ext; simp; omega
  · rename_i ho
    have hlt : x.2.val/2 < r := by omega
    simp only [vertexDecode,dite_eq_left hlt]
    apply Prod.ext
    · rfl
    · apply Fin.ext; simp; omega

theorem vertexCode_decode (h r : Nat) (x : Rectangle h (2*r+1)) :
    vertexCode h r (vertexDecode h r x)=x := by
  unfold vertexDecode
  split
  · rename_i hlt
    have ho : ¬ (2*x.2.val+1)%2=0 := by omega
    simp only [vertexCode,ho,ite_false]
    apply Prod.ext
    · rfl
    · apply Fin.ext; simp; omega
  · rename_i hge
    have he : (2*(2*r-x.2.val))%2=0 := by omega
    simp only [vertexCode,he,ite_true,mirror_mirror]
    apply Prod.ext
    · rfl
    · apply Fin.ext; simp; omega

theorem residual_arm_code (h m r : Nat) (i : Fin h) (d : Fin (2*r+1)) :
    residualLabel h m (2*r+1) (.arm i d)=flatLabel h (2*r+1) (vertexCode h r (i,d)) := by
  by_cases he : d.val%2=0
  · have hid : h-i.val=(h-1-i.val)+1 := by omega
    have hprod := congrArg (fun a => a*(2*r+1)) hid
    simp only [Nat.add_mul,Nat.one_mul] at hprod
    simp only [residualLabel,vertexCode,he,ite_true,flatLabel,mirror]
    omega
  · simp only [residualLabel,vertexCode,he,ite_false,flatLabel]
    omega

theorem residual_arm_band (h m r : Nat) :
    BandBijection (fun x : Rectangle h (2*r+1) => residualLabel h m (2*r+1) (.arm x.1 x.2))
      1 (h*(2*r+1)) := by
  have hb := band_precompose (flatLabel h (2*r+1)) 1 (h*(2*r+1))
    (rectangle_band h (2*r+1) (by omega)) (vertexCode h r) (vertexDecode h r)
    (vertexDecode_code h r) (vertexCode_decode h r)
  have heq : (fun x : Rectangle h (2*r+1) => residualLabel h m (2*r+1) (.arm x.1 x.2))=
      (fun x => flatLabel h (2*r+1) (vertexCode h r x)) := by
    funext x
    exact residual_arm_code h m r x.1 x.2
  rw [heq]
  exact hb


theorem residual_vertex_band (h m r : Nat) :
    BandBijection (residualLabel h m (2*r+1)) 0 (h*(2*r+1)+m) := by
  have ha := residual_arm_band h m r
  constructor
  · intro v
    cases v with
    | center => simp [residualLabel]
    | arm i d => have hb := ha.bounds (i,d); dsimp only at hb; simpa only [residualLabel] using And.intro (by omega : 0 ≤ residualLabel h m (2*r+1) (.arm i d)) (by omega : residualLabel h m (2*r+1) (.arm i d) ≤ h*(2*r+1)+m)
    | leaf j => simp only [residualLabel]; omega
  · intro v w he
    cases v with
    | center =>
      cases w with
      | center => rfl
      | arm i d => have hb := ha.bounds (i,d); dsimp only at hb; change 0=residualLabel h m (2*r+1) (.arm i d) at he; omega
      | leaf j => simp [residualLabel] at he
    | arm i d =>
      cases w with
      | center => have hb := ha.bounds (i,d); dsimp only at hb; change residualLabel h m (2*r+1) (.arm i d)=0 at he; omega
      | arm j e =>
        have hp := ha.injective (i,d) (j,e) he
        have hi : i=j := congrArg Prod.fst hp
        have hd : d=e := congrArg Prod.snd hp
        subst j; subst e; rfl
      | leaf j =>
        have hb := ha.bounds (i,d)
        dsimp only at hb
        change residualLabel h m (2*r+1) (.arm i d)=h*(2*r+1)+j.val+1 at he
        omega
    | leaf j =>
      cases w with
      | center => simp [residualLabel] at he
      | arm i d =>
        have hb := ha.bounds (i,d)
        dsimp only at hb
        change h*(2*r+1)+j.val+1=residualLabel h m (2*r+1) (.arm i d) at he
        omega
      | leaf k =>
        have hval : j.val=k.val := by simp only [residualLabel] at he; omega
        exact congrArg SpiderVertex.leaf (Fin.ext hval)
  · intro x _ hx
    by_cases hz : x=0
    · exact ⟨.center,by simp [residualLabel,hz]⟩
    by_cases haBound : x ≤ h*(2*r+1)
    · obtain ⟨a,he⟩ := ha.onto x (by omega) haBound
      exact ⟨.arm a.1 a.2,he⟩
    · refine ⟨.leaf ⟨x-h*(2*r+1)-1,by omega⟩,?_⟩
      simp only [residualLabel]
      omega

/-- The open-block permutation in the residual internal-edge proof. -/
def foldedIndex (h : Nat) (i : Fin h) : Fin h :=
  if hi : 2*i.val<h then ⟨h-2*i.val-1,by omega⟩ else ⟨2*i.val-h,by omega⟩

def unfoldedIndex (h : Nat) (j : Fin h) : Fin h :=
  if hj : (h+j.val)%2=0 then ⟨(h+j.val)/2,by omega⟩ else ⟨(h-j.val-1)/2,by omega⟩

theorem unfolded_folded (h : Nat) (i : Fin h) : unfoldedIndex h (foldedIndex h i)=i := by
  unfold foldedIndex
  split
  · rename_i hi
    have hj : ¬ (h+(h-2*i.val-1))%2=0 := by omega
    simp only [unfoldedIndex,dite_eq_right hj]
    apply Fin.ext
    simp only
    omega
  · rename_i hi
    have hj : (h+(2*i.val-h))%2=0 := by omega
    simp only [unfoldedIndex,dite_eq_left hj]
    apply Fin.ext
    simp only
    omega

theorem folded_unfolded (h : Nat) (j : Fin h) : foldedIndex h (unfoldedIndex h j)=j := by
  unfold unfoldedIndex
  split
  · rename_i hj
    have hi : ¬ 2*((h+j.val)/2)<h := by omega
    simp only [foldedIndex,dite_eq_right hi]
    apply Fin.ext
    simp only
    omega
  · rename_i hj
    have hi : 2*((h-j.val-1)/2)<h := by omega
    simp only [foldedIndex,dite_eq_left hi]
    apply Fin.ext
    simp only
    omega

def edgeCode (h k : Nat) (hk : 0 < k) (x : Rectangle h k) : Rectangle h k :=
  if hd : x.2.val=0 then (mirror h x.1,⟨k-1,by omega⟩)
  else (foldedIndex h x.1,
    if hi : 2*x.1.val<h then ⟨k-x.2.val-1,by omega⟩ else ⟨x.2.val-1,by omega⟩)

def edgeDecode (h k : Nat) (hk : 0 < k) (x : Rectangle h k) : Rectangle h k :=
  if hd : x.2.val=k-1 then (mirror h x.1,⟨0,hk⟩)
  else (unfoldedIndex h x.1,
    if hi : 2*(unfoldedIndex h x.1).val<h then ⟨k-x.2.val-1,by omega⟩ else ⟨x.2.val+1,by omega⟩)

theorem edgeDecode_code (h k : Nat) (hk : 0 < k) (x : Rectangle h k) :
    edgeDecode h k hk (edgeCode h k hk x)=x := by
  unfold edgeCode
  split
  · rename_i hd
    simp only [edgeDecode,dite_true,mirror_mirror]
    apply Prod.ext
    · rfl
    · apply Fin.ext; dsimp only; omega
  · rename_i hd
    split
    · rename_i hi
      have hz : ¬ k-x.2.val-1=k-1 := by omega
      simp only [edgeDecode,dite_eq_right hz,unfolded_folded,dite_eq_left hi]
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp only; omega
    · rename_i hi
      have hz : ¬ x.2.val-1=k-1 := by omega
      simp only [edgeDecode,dite_eq_right hz,unfolded_folded,dite_eq_right hi]
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp only; omega

theorem edgeCode_decode (h k : Nat) (hk : 0 < k) (x : Rectangle h k) :
    edgeCode h k hk (edgeDecode h k hk x)=x := by
  unfold edgeDecode
  split
  · rename_i hd
    simp only [edgeCode,dite_true,mirror_mirror]
    apply Prod.ext
    · rfl
    · apply Fin.ext; dsimp only; omega
  · rename_i hd
    split
    · rename_i hi
      have hz : ¬ k-x.2.val-1=0 := by omega
      simp only [edgeCode,dite_eq_right hz,folded_unfolded,dite_eq_left hi]
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp only; omega
    · rename_i hi
      have hz : ¬ x.2.val+1=0 := by omega
      simp only [edgeCode,dite_eq_right hz,folded_unfolded,dite_eq_right hi]
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp only; omega

theorem residual_arm_weight_code (h m r : Nat) (i : Fin h) (d : Fin (2*r+1)) :
    weight (spiderGraph h m (2*r+1)) (residualLabel h m (2*r+1)) (.arm i d)=
      flatLabel h (2*r+1) (edgeCode h (2*r+1) (by omega) (i,d)) := by
  by_cases hd : d.val=0
  · have hid : h-i.val=(h-1-i.val)+1 := by omega
    have hp := congrArg (fun a => a*(2*r+1)) hid
    simp only [Nat.add_mul,Nat.one_mul] at hp
    simp only [weight,spiderGraph,residualLabel,hd,ite_true,dite_true,edgeCode,flatLabel,mirror,distance,Nat.zero_mod,Nat.zero_div,Nat.sub_zero,Nat.zero_sub]
    omega
  · have hmul := Nat.mul_le_mul_right (2*r+1) (show 1 ≤ h-i.val by omega)
    simp only [Nat.one_mul] at hmul
    by_cases hi : 2*i.val<h
    · have hid : h-i.val=i.val+(h-2*i.val-1)+1 := by omega
      have hp := congrArg (fun a => a*(2*r+1)) hid
      simp only [Nat.add_mul,Nat.one_mul] at hp
      by_cases he : d.val%2=0
      · have hpred : ¬ (d.val-1)%2=0 := by omega
        simp only [weight,spiderGraph,residualLabel,hd,he,hpred,ite_true,ite_false,dite_true,dite_false,edgeCode,flatLabel,foldedIndex,hi,distance]
        omega
      · have hpred : (d.val-1)%2=0 := by omega
        simp only [weight,spiderGraph,residualLabel,hd,he,hpred,ite_true,ite_false,dite_true,dite_false,edgeCode,flatLabel,foldedIndex,hi,distance]
        omega
    · have hid : i.val=(h-i.val)+(2*i.val-h) := by omega
      have hp := congrArg (fun a => a*(2*r+1)) hid
      simp only [Nat.add_mul] at hp
      by_cases he : d.val%2=0
      · have hpred : ¬ (d.val-1)%2=0 := by omega
        simp only [weight,spiderGraph,residualLabel,hd,he,hpred,ite_true,ite_false,dite_false,edgeCode,flatLabel,foldedIndex,hi,distance]
        omega
      · have hpred : (d.val-1)%2=0 := by omega
        simp only [weight,spiderGraph,residualLabel,hd,he,hpred,ite_true,ite_false,dite_false,edgeCode,flatLabel,foldedIndex,hi,distance]
        omega

theorem residual_arm_edge_band (h m r : Nat) :
    BandBijection (fun x : Rectangle h (2*r+1) =>
      weight (spiderGraph h m (2*r+1)) (residualLabel h m (2*r+1)) (.arm x.1 x.2))
      1 (h*(2*r+1)) := by
  have hk : 0 < 2*r+1 := by omega
  have hb := band_precompose (flatLabel h (2*r+1)) 1 (h*(2*r+1))
    (rectangle_band h (2*r+1) hk) (edgeCode h (2*r+1) hk) (edgeDecode h (2*r+1) hk)
    (edgeDecode_code h (2*r+1) hk) (edgeCode_decode h (2*r+1) hk)
  have heq : (fun x : Rectangle h (2*r+1) =>
      weight (spiderGraph h m (2*r+1)) (residualLabel h m (2*r+1)) (.arm x.1 x.2))=
      (fun x => flatLabel h (2*r+1) (edgeCode h (2*r+1) hk x)) := by
    funext x
    exact residual_arm_weight_code h m r x.1 x.2
  rw [heq]
  exact hb

theorem residual_leaf_weight (h m k : Nat) (j : Fin m) :
    weight (spiderGraph h m k) (residualLabel h m k) (.leaf j)=h*k+j.val+1 := by
  simp [weight,spiderGraph,residualLabel,distance]

theorem residual_edge_band (h m r : Nat) :
    BandBijection (weight (spiderGraph h m (2*r+1)) (residualLabel h m (2*r+1))) 1 (h*(2*r+1)+m) := by
  have ha := residual_arm_edge_band h m r
  constructor
  · intro e
    cases e with
    | arm i d =>
      have hb := ha.bounds (i,d)
      dsimp only at hb
      constructor <;> omega
    | leaf j => rw [residual_leaf_weight]; constructor <;> omega
  · intro e e' he
    cases e with
    | arm i d =>
      cases e' with
      | arm j d' =>
        have hp := ha.injective (i,d) (j,d') he
        have hi : i=j := congrArg Prod.fst hp
        have hd : d=d' := congrArg Prod.snd hp
        subst j; subst d'; rfl
      | leaf j =>
        rw [residual_leaf_weight] at he
        have hb := ha.bounds (i,d)
        dsimp only at hb
        omega
    | leaf j =>
      cases e' with
      | arm i d =>
        rw [residual_leaf_weight] at he
        have hb := ha.bounds (i,d)
        dsimp only at hb
        omega
      | leaf j' =>
        rw [residual_leaf_weight,residual_leaf_weight] at he
        exact congrArg SpiderEdge.leaf (Fin.ext (by omega))
  · intro x hx ht
    by_cases hb : x ≤ h*(2*r+1)
    · obtain ⟨a,he⟩ := ha.onto x hx hb
      exact ⟨.arm a.1 a.2,he⟩
    · refine ⟨.leaf ⟨x-h*(2*r+1)-1,by omega⟩,?_⟩
      rw [residual_leaf_weight]
      dsimp only
      omega

/-- The inherited center-zero spider formula, now proved for all parameters. -/
theorem residual_gracefulness : ResidualGracefulness := by
  intro h m r
  exact ⟨residual_vertex_band h m r,residual_edge_band h m r⟩
end GracefulBoundary










