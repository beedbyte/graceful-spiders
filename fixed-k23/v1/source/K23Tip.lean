import K23Leaf

namespace GracefulBoundary.K23Tip

abbrev TailVertex (h m : Nat) := Sum (SpiderVertex h m 23) (Fin 23)
abbrev TailEdge (h m : Nat) := Sum (SpiderEdge h m 23) (Fin 23)

def tailGraph (h m : Nat) : IndexedGraph (TailVertex h m) (TailEdge h m) where
  source := fun e => match e with
    | .inl e => .inl ((spiderGraph h m 23).source e)
    | .inr d => if d.val=0 then .inl .center else .inr ⟨d.val-1,by omega⟩
  target := fun e => match e with
    | .inl e => .inl ((spiderGraph h m 23).target e)
    | .inr d => .inr d

def tailLabel (h m : Nat) : TailVertex h m → Nat
  | .inl v => h*23+m+12-residualLabel h m 23 v
  | .inr d => if d.val%2=0 then 11-d.val/2 else h*23+m+13+d.val/2

theorem tail_low_high (h m : Nat) (d : Fin 23) :
    (d.val%2=0 → tailLabel h m (.inr d) ≤ 11) ∧
    (d.val%2≠0 → h*23+m+13 ≤ tailLabel h m (.inr d) ∧
      tailLabel h m (.inr d) ≤ h*23+m+23) := by
  have := d.isLt
  simp only [tailLabel]
  constructor <;> intro he <;> simp only [he,ite_true,ite_false] <;> omega

theorem tail_vertices (h m : Nat) : BandBijection (tailLabel h m) 0 (h*23+m+23) := by
  have hr : Graceful (spiderGraph h m 23) (h*23+m) (residualLabel h m 23) := residual_gracefulness h m 11
  have hf := hr.vertices
  constructor
  · intro v
    cases v with
    | inl v => have hb := hf.bounds v; simp only [tailLabel]; omega
    | inr d =>
      have := d.isLt
      simp only [tailLabel]
      split <;> omega
  · intro v w he
    cases v with
    | inl v =>
      have hv := hf.bounds v
      cases w with
      | inl w =>
        have hw := hf.bounds w
        have hsame : residualLabel h m 23 v=residualLabel h m 23 w := by
          simp only [tailLabel] at he; omega
        exact congrArg Sum.inl (hf.injective _ _ hsame)
      | inr d =>
        have := d.isLt
        simp only [tailLabel] at he
        split at he <;> omega
    | inr d =>
      cases w with
      | inl w =>
        have hw := hf.bounds w
        have := d.isLt
        simp only [tailLabel] at he
        split at he <;> omega
      | inr e =>
        have hd := d.isLt
        have he' := e.isLt
        apply congrArg Sum.inr
        apply Fin.ext
        simp only [tailLabel] at he
        split at he <;> split at he <;> omega
  · intro x _ hx
    by_cases hlo : x≤11
    · refine ⟨.inr ⟨22-2*x,by omega⟩,?_⟩
      simp only [tailLabel]
      have he : (22-2*x)%2=0 := by omega
      rw [ite_eq_left he]
      omega
    · by_cases hmid : x≤h*23+m+12
      · obtain ⟨v,hv⟩ := hf.onto (h*23+m+12-x) (by omega) (by omega)
        exact ⟨.inl v,by simp only [tailLabel,hv]; omega⟩
      · refine ⟨.inr ⟨2*(x-(h*23+m+13))+1,by omega⟩,?_⟩
        simp only [tailLabel]
        have he : (2*(x-(h*23+m+13))+1)%2≠0 := by omega
        rw [ite_eq_right he]
        omega

theorem tail_residual_weight (h m : Nat) (e : SpiderEdge h m 23) :
    weight (tailGraph h m) (tailLabel h m) (.inl e)=
      weight (spiderGraph h m 23) (residualLabel h m 23) e := by
  have hr : Graceful (spiderGraph h m 23) (h*23+m) (residualLabel h m 23) := residual_gracefulness h m 11
  have hs := (hr.vertices.bounds ((spiderGraph h m 23).source e)).2
  have ht := (hr.vertices.bounds ((spiderGraph h m 23).target e)).2
  exact complement_difference (h*23+m+12) _ _ (by omega) (by omega)

theorem tail_new_weight (h m : Nat) (d : Fin 23) :
    weight (tailGraph h m) (tailLabel h m) (.inr d)=h*23+m+d.val+1 := by
  have hd := d.isLt
  by_cases hz : d.val=0
  · simp only [weight,tailGraph,hz,ite_true,tailLabel,residualLabel]
    simp only [distance]
    omega
  · simp only [weight,tailGraph,ite_eq_right hz,tailLabel]
    split <;> split <;> simp only [distance] <;> omega

theorem tail_graceful (h m : Nat) : Graceful (tailGraph h m) (h*23+m+23) (tailLabel h m) := by
  have hr : Graceful (spiderGraph h m 23) (h*23+m) (residualLabel h m 23) := residual_gracefulness h m 11
  have hf := hr.edges
  refine ⟨tail_vertices h m,?_⟩
  constructor
  · intro e
    cases e with
    | inl e => rw [tail_residual_weight]; have hb := hf.bounds e; omega
    | inr d => rw [tail_new_weight]; have := d.isLt; omega
  · intro e f he
    cases e with
    | inl e =>
      cases f with
      | inl f => rw [tail_residual_weight,tail_residual_weight] at he; exact congrArg Sum.inl (hf.injective _ _ he)
      | inr d => rw [tail_residual_weight,tail_new_weight] at he; have := hf.bounds e; omega
    | inr d =>
      cases f with
      | inl f => rw [tail_new_weight,tail_residual_weight] at he; have := hf.bounds f; omega
      | inr e => rw [tail_new_weight,tail_new_weight] at he; exact congrArg Sum.inr (Fin.ext (by omega))
  · intro x hx ht
    by_cases hlo : x≤h*23+m
    · obtain ⟨e,he⟩ := hf.onto x hx hlo
      exact ⟨.inl e,by rw [tail_residual_weight,he]⟩
    · refine ⟨.inr ⟨x-(h*23+m)-1,by omega⟩,?_⟩
      rw [tail_new_weight]
      change h*23+m+(x-(h*23+m)-1)+1=x
      omega

def tailToSpider (h m : Nat) : TailVertex h m → SpiderVertex (h+1) m 23
  | .inl .center => .center
  | .inl (.leaf j) => .leaf j
  | .inl (.arm i d) => .arm ⟨i.val+1,by omega⟩ d
  | .inr d => .arm ⟨0,by omega⟩ d

def spiderToTail (h m : Nat) : SpiderVertex (h+1) m 23 → TailVertex h m
  | .center => .inl .center
  | .leaf j => .inl (.leaf j)
  | .arm i d => if hi : i.val=0 then .inr d else .inl (.arm ⟨i.val-1,by omega⟩ d)

def tailEdgeToSpider (h m : Nat) : TailEdge h m → SpiderEdge (h+1) m 23
  | .inl (.leaf j) => .leaf j
  | .inl (.arm i d) => .arm ⟨i.val+1,by omega⟩ d
  | .inr d => .arm ⟨0,by omega⟩ d

def spiderEdgeToTail (h m : Nat) : SpiderEdge (h+1) m 23 → TailEdge h m
  | .leaf j => .inl (.leaf j)
  | .arm i d => if hi : i.val=0 then .inr d else .inl (.arm ⟨i.val-1,by omega⟩ d)

theorem tail_vertex_left (h m : Nat) (v : SpiderVertex (h+1) m 23) :
    tailToSpider h m (spiderToTail h m v)=v := by
  cases v with
  | center => rfl
  | leaf j => rfl
  | arm i d =>
    simp only [spiderToTail]
    split <;> simp only [tailToSpider] <;> congr 1 <;> apply Fin.ext <;> dsimp only <;> omega

theorem tail_vertex_right (h m : Nat) (v : TailVertex h m) :
    spiderToTail h m (tailToSpider h m v)=v := by
  cases v with
  | inr d => simp [tailToSpider,spiderToTail]
  | inl v =>
    cases v with
    | center => rfl
    | leaf j => rfl
    | arm i d =>
      simp only [tailToSpider,spiderToTail]
      rw [dite_eq_right (by omega)]
      congr 2

theorem tail_edge_left (h m : Nat) (e : SpiderEdge (h+1) m 23) :
    tailEdgeToSpider h m (spiderEdgeToTail h m e)=e := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    simp only [spiderEdgeToTail]
    split <;> simp only [tailEdgeToSpider] <;> congr 1 <;> apply Fin.ext <;> dsimp only <;> omega

theorem tail_edge_right (h m : Nat) (e : TailEdge h m) :
    spiderEdgeToTail h m (tailEdgeToSpider h m e)=e := by
  cases e with
  | inr d => simp [tailEdgeToSpider,spiderEdgeToTail]
  | inl e =>
    cases e with
    | leaf j => rfl
    | arm i d =>
      simp only [tailEdgeToSpider,spiderEdgeToTail]
      rw [dite_eq_right (by omega)]
      congr 2

theorem tail_spider_weights (h m : Nat) (f : TailVertex h m → Nat)
    (e : SpiderEdge (h+1) m 23) :
    weight (spiderGraph (h+1) m 23) (fun v => f (spiderToTail h m v)) e =
      weight (tailGraph h m) f (spiderEdgeToTail h m e) := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    by_cases hi : i.val=0 <;> by_cases hd : d.val=0 <;>
      simp only [weight,spiderGraph,tailGraph,spiderEdgeToTail,spiderToTail,hi,hd,ite_true,ite_false,dite_true,dite_false]

theorem tip_first_arm (h m : Nat) :
    ∃ f : SpiderVertex (h+1) m 23 → Nat,
      Graceful (spiderGraph (h+1) m 23) ((h+1)*23+m) f ∧
      f (.arm ⟨0,by omega⟩ ⟨22,by decide⟩)=0 ∧
      f (.arm ⟨0,by omega⟩ ⟨21,by decide⟩)=(h+1)*23+m := by
  have hg := graceful_transport (tailGraph h m) (spiderGraph (h+1) m 23) (h*23+m+23)
    (tailLabel h m) (tail_graceful h m) (spiderToTail h m) (tailToSpider h m)
    (spiderEdgeToTail h m) (tailEdgeToSpider h m)
    (tail_vertex_left h m) (tail_vertex_right h m) (tail_edge_left h m) (tail_edge_right h m)
    (tail_spider_weights h m (tailLabel h m))
  have he : h*23+m+23=(h+1)*23+m := by simp only [Nat.add_mul]; omega
  rw [he] at hg
  refine ⟨fun v => tailLabel h m (spiderToTail h m v),hg,?_,?_⟩
  · rfl
  · change h*23+m+13+10=(h+1)*23+m
    simp only [Nat.add_mul]; omega

theorem tips_prescribed_zero (n m : Nat) (hn : 1 ≤ n) (a : Fin n) :
    (∃ f : SpiderVertex n m 23 → Nat,Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨22,by decide⟩)=0) ∧
    (∃ f : SpiderVertex n m 23 → Nat,Graceful (spiderGraph n m 23) (n*23+m) f ∧ f (.arm a ⟨21,by decide⟩)=0) := by
  obtain ⟨h,rfl⟩ : ∃ h,n=h+1 := ⟨n-1,by omega⟩
  obtain ⟨f,hf,hzero,hmax⟩ := tip_first_arm h m
  let z : Fin (h+1) := ⟨0,by omega⟩
  let g := fun v => f (swapVertex a z v)
  have hg : Graceful (spiderGraph (h+1) m 23) ((h+1)*23+m) g := graceful_swap a z f hf
  have gz : g (.arm a ⟨22,by decide⟩)=0 := by simpa only [g,swapVertex,swapIndex_first] using hzero
  have gm : g (.arm a ⟨21,by decide⟩)=(h+1)*23+m := by simpa only [g,swapVertex,swapIndex_first] using hmax
  refine ⟨⟨g,hg,gz⟩,⟨fun v => (h+1)*23+m-g v,graceful_complement _ _ g hg,?_⟩⟩
  simp only [gm,Nat.sub_self]

end GracefulBoundary.K23Tip

