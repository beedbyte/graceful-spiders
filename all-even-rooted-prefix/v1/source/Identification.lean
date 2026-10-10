import Graft
namespace GracefulBoundary

 theorem graceful_transport {V E W F : Type} (G : IndexedGraph V E) (H : IndexedGraph W F)
    (M : Nat) (f : V → Nat) (hf : Graceful G M f)
    (v : W → V) (vi : V → W) (e : F → E) (ei : E → F)
    (vl : ∀ x, vi (v x)=x) (vr : ∀ x, v (vi x)=x)
    (el : ∀ x, ei (e x)=x) (er : ∀ x, e (ei x)=x)
    (hw : ∀ x, weight H (fun x => f (v x)) x=weight G f (e x)) :
    Graceful H M (fun x => f (v x)) := by
  constructor
  · exact band_precompose f 0 M hf.vertices v vi vl vr
  · have h := band_precompose (weight G f) 1 M hf.edges e ei el er
    have he : weight H (fun x => f (v x)) = fun x => weight G f (e x) := funext hw
    rw [he]
    exact h

def leftVertex (s : Nat) (d : Fin (6*s+3)) : {v : Fin (12*s+7) // v ≠ boundaryCenter s} :=
  ⟨⟨6*s+2-d.val,by omega⟩,by intro he; have := congrArg Fin.val he; simp only [boundaryCenter] at this; omega⟩
def rightVertex (s : Nat) (d : Fin (6*s+3)) : {v : Fin (12*s+7) // v ≠ boundaryCenter s} :=
  ⟨⟨6*s+4+d.val,by omega⟩,by intro he; have := congrArg Fin.val he; simp only [boundaryCenter] at this; omega⟩

def spiderToGraft (s h m : Nat) : SpiderVertex (h+2) m (6*s+3) → BoundaryGraftVertex s h m
  | .center => .inr .center
  | .leaf j => .inr (.leaf j)
  | .arm i d => if h0 : i.val=0 then .inl (leftVertex s d)
    else if h1 : i.val=1 then .inl (rightVertex s d)
    else .inr (.arm ⟨i.val-2,by omega⟩ d)

def graftToSpider (s h m : Nat) : BoundaryGraftVertex s h m → SpiderVertex (h+2) m (6*s+3)
  | .inr .center => .center
  | .inr (.leaf j) => .leaf j
  | .inr (.arm i d) => .arm ⟨i.val+2,by omega⟩ d
  | .inl v => if hv : v.val.val < 6*s+3 then
      .arm ⟨0,by omega⟩ ⟨6*s+2-v.val.val,by omega⟩
    else .arm ⟨1,by omega⟩ ⟨v.val.val-(6*s+4),by have := v.val.isLt; omega⟩

theorem graftToSpider_left (s h m : Nat) (d : Fin (6*s+3)) :
    graftToSpider s h m (.inl (leftVertex s d)) = .arm ⟨0,by omega⟩ d := by
  dsimp only [graftToSpider,leftVertex]
  rw [dite_eq_left (by omega)]
  congr 1
  apply Fin.ext
  dsimp only
  omega

theorem graftToSpider_right (s h m : Nat) (d : Fin (6*s+3)) :
    graftToSpider s h m (.inl (rightVertex s d)) = .arm ⟨1,by omega⟩ d := by
  dsimp only [graftToSpider,rightVertex]
  rw [dite_eq_right (by omega)]
  congr 1
  apply Fin.ext
  dsimp only
  omega

theorem graft_spider_left_inverse (s h m : Nat) (v : SpiderVertex (h+2) m (6*s+3)) :
    graftToSpider s h m (spiderToGraft s h m v)=v := by
  cases v with
  | center => rfl
  | leaf j => rfl
  | arm i d =>
    simp only [spiderToGraft]
    by_cases h0 : i.val=0
    · rw [dite_eq_left h0,graftToSpider_left]
      congr 1; apply Fin.ext; exact h0.symm
    · rw [dite_eq_right h0]
      by_cases h1 : i.val=1
      · rw [dite_eq_left h1,graftToSpider_right]
        congr 1; apply Fin.ext; exact h1.symm
      · rw [dite_eq_right h1]
        simp only [graftToSpider]
        congr 1; apply Fin.ext; dsimp only; omega

theorem graft_spider_right_inverse (s h m : Nat) (v : BoundaryGraftVertex s h m) :
    spiderToGraft s h m (graftToSpider s h m v)=v := by
  cases v with
  | inr v =>
    cases v with
    | center => rfl
    | leaf j => rfl
    | arm i d =>
      simp only [graftToSpider,spiderToGraft]
      rw [dite_eq_right (by omega),dite_eq_right (by omega)]
      congr 2
  | inl v =>
    have hn : v.val.val ≠ 6*s+3 := by
      intro he; apply v.property; apply Fin.ext; exact he
    simp only [graftToSpider]
    split
    · simp only [spiderToGraft,dite_true]
      congr 1; apply Subtype.ext; apply Fin.ext
      simp only [leftVertex]; omega
    · simp only [spiderToGraft,show (1:Nat)≠0 by omega,dite_false,dite_true]
      congr 1; apply Subtype.ext; apply Fin.ext
      simp only [rightVertex]; omega

abbrev BoundaryGraftEdge (s h m : Nat) := Sum (Fin (12*s+6)) (SpiderEdge h m (6*s+3))
def spiderEdgeToGraft (s h m : Nat) : SpiderEdge (h+2) m (6*s+3) → BoundaryGraftEdge s h m
  | .leaf j => .inr (.leaf j)
  | .arm i d => if h0 : i.val=0 then .inl ⟨6*s+2-d.val,by omega⟩
    else if h1 : i.val=1 then .inl ⟨6*s+3+d.val,by omega⟩
    else .inr (.arm ⟨i.val-2,by omega⟩ d)
def graftEdgeToSpider (s h m : Nat) : BoundaryGraftEdge s h m → SpiderEdge (h+2) m (6*s+3)
  | .inr (.leaf j) => .leaf j
  | .inr (.arm i d) => .arm ⟨i.val+2,by omega⟩ d
  | .inl e => if he : e.val < 6*s+3 then .arm ⟨0,by omega⟩ ⟨6*s+2-e.val,by omega⟩
    else .arm ⟨1,by omega⟩ ⟨e.val-(6*s+3),by omega⟩

theorem edge_graft_spider_left_inverse (s h m : Nat) (e : SpiderEdge (h+2) m (6*s+3)) :
    graftEdgeToSpider s h m (spiderEdgeToGraft s h m e)=e := by
  cases e with
  | leaf j => rfl
  | arm i d =>
    simp only [spiderEdgeToGraft]
    by_cases h0 : i.val=0
    · rw [dite_eq_left h0]
      simp only [graftEdgeToSpider]
      rw [dite_eq_left (by omega)]
      congr 1
      · apply Fin.ext; exact h0.symm
      · apply Fin.ext; dsimp only; omega
    · rw [dite_eq_right h0]
      by_cases h1 : i.val=1
      · rw [dite_eq_left h1]
        simp only [graftEdgeToSpider]
        rw [dite_eq_right (by omega)]
        congr 1
        · apply Fin.ext; exact h1.symm
        · apply Fin.ext; dsimp only; omega
      · rw [dite_eq_right h1]
        simp only [graftEdgeToSpider]
        congr 1; apply Fin.ext; dsimp only; omega

theorem edge_graft_spider_right_inverse (s h m : Nat) (e : BoundaryGraftEdge s h m) :
    spiderEdgeToGraft s h m (graftEdgeToSpider s h m e)=e := by
  cases e with
  | inr e =>
    cases e with
    | leaf j => rfl
    | arm i d =>
      simp only [graftEdgeToSpider,spiderEdgeToGraft]
      rw [dite_eq_right (by omega),dite_eq_right (by omega)]
      congr 2
  | inl e =>
    simp only [graftEdgeToSpider]
    split
    · simp only [spiderEdgeToGraft,dite_true]
      congr 1; apply Fin.ext; dsimp only; omega
    · simp only [spiderEdgeToGraft,show (1:Nat)≠0 by omega,dite_false,dite_true]
      congr 1; apply Fin.ext; dsimp only; omega




theorem embed_left (s h m : Nat) (d : Fin (6*s+3)) :
    graftEmbed (boundaryCenter s) (SpiderVertex.center : SpiderVertex h m (6*s+3))
      (leftVertex s d).val = Sum.inl (leftVertex s d) := by
  simp only [graftEmbed,dite_eq_right (leftVertex s d).property]

theorem embed_right (s h m : Nat) (d : Fin (6*s+3)) :
    graftEmbed (boundaryCenter s) (SpiderVertex.center : SpiderVertex h m (6*s+3))
      (rightVertex s d).val = Sum.inl (rightVertex s d) := by
  simp only [graftEmbed,dite_eq_right (rightVertex s d).property]

theorem graft_spider_weights (s h m : Nat) (f : BoundaryGraftVertex s h m → Nat)
    (e : SpiderEdge (h+2) m (6*s+3)) :
    weight (spiderGraph (h+2) m (6*s+3)) (fun v => f (spiderToGraft s h m v)) e =
      weight (boundaryGraftGraph s h m) f (spiderEdgeToGraft s h m e) := by
  classical
  cases e with
  | leaf j => rfl
  | arm i d =>
    by_cases h0 : i.val=0
    · have ht : spiderToGraft s h m (.arm i d) =
          (boundaryGraftGraph s h m).source (spiderEdgeToGraft s h m (.arm i d)) := by
        simp only [spiderToGraft,spiderEdgeToGraft,dite_eq_left h0,boundaryGraftGraph,graftGraph,pathGraph]
        exact (embed_left s h m d).symm
      have hs : spiderToGraft s h m ((spiderGraph (h+2) m (6*s+3)).source (.arm i d)) =
          (boundaryGraftGraph s h m).target (spiderEdgeToGraft s h m (.arm i d)) := by
        simp only [spiderEdgeToGraft,dite_eq_left h0,boundaryGraftGraph,graftGraph,pathGraph,spiderGraph]
        by_cases hd : d.val=0
        · rw [ite_eq_left hd]
          have he : (⟨6*s+2-d.val+1,by omega⟩ : Fin (12*s+7))=boundaryCenter s := by
            apply Fin.ext; dsimp only [boundaryCenter]; omega
          rw [he]
          simp only [spiderToGraft,graftEmbed,dite_true]
        · rw [ite_eq_right hd]
          simp only [spiderToGraft,dite_eq_left h0]
          have he : (⟨6*s+2-d.val+1,by omega⟩ : Fin (12*s+7))=
              (leftVertex s ⟨d.val-1,by omega⟩).val := by
            apply Fin.ext; dsimp only [leftVertex]; omega
          rw [he,embed_left]
      change distance (f (spiderToGraft s h m ((spiderGraph (h+2) m (6*s+3)).source (.arm i d))))
        (f (spiderToGraft s h m (.arm i d))) = _
      rw [hs,ht]
      exact distance_comm _ _
    · by_cases h1 : i.val=1
      · have ht : spiderToGraft s h m (.arm i d) =
            (boundaryGraftGraph s h m).target (spiderEdgeToGraft s h m (.arm i d)) := by
          simp only [spiderToGraft,spiderEdgeToGraft,dite_eq_right h0,dite_eq_left h1,boundaryGraftGraph,graftGraph,pathGraph]
          have he : (⟨6*s+3+d.val+1,by omega⟩ : Fin (12*s+7))=(rightVertex s d).val := by
            apply Fin.ext; dsimp only [rightVertex]; omega
          rw [he,embed_right]
        have hs : spiderToGraft s h m ((spiderGraph (h+2) m (6*s+3)).source (.arm i d)) =
            (boundaryGraftGraph s h m).source (spiderEdgeToGraft s h m (.arm i d)) := by
          simp only [spiderEdgeToGraft,dite_eq_right h0,dite_eq_left h1,boundaryGraftGraph,graftGraph,pathGraph,spiderGraph]
          by_cases hd : d.val=0
          · rw [ite_eq_left hd]
            have he : (⟨6*s+3+d.val,by omega⟩ : Fin (12*s+7))=boundaryCenter s := by
              apply Fin.ext; dsimp only [boundaryCenter]; omega
            rw [he]
            simp only [spiderToGraft,graftEmbed,dite_true]
          · rw [ite_eq_right hd]
            simp only [spiderToGraft,dite_eq_right h0,dite_eq_left h1]
            have he : (⟨6*s+3+d.val,by omega⟩ : Fin (12*s+7))=
                (rightVertex s ⟨d.val-1,by omega⟩).val := by
              apply Fin.ext; dsimp only [rightVertex]; omega
            rw [he,embed_right]
        change distance (f (spiderToGraft s h m ((spiderGraph (h+2) m (6*s+3)).source (.arm i d))))
          (f (spiderToGraft s h m (.arm i d))) = _
        rw [hs,ht]
        rfl
      · by_cases hd : d.val=0 <;>
          simp only [weight,spiderGraph,spiderEdgeToGraft,dite_eq_right h0,dite_eq_right h1,
            boundaryGraftGraph,graftGraph,spiderToGraft,hd,ite_true,ite_false]




theorem graft_graceful_on_spider (s h m M : Nat) (f : BoundaryGraftVertex s h m → Nat)
    (hf : Graceful (boundaryGraftGraph s h m) M f) :
    Graceful (spiderGraph (h+2) m (6*s+3)) M (fun v => f (spiderToGraft s h m v)) :=
  graceful_transport (boundaryGraftGraph s h m) (spiderGraph (h+2) m (6*s+3)) M f hf
    (spiderToGraft s h m) (graftToSpider s h m) (spiderEdgeToGraft s h m) (graftEdgeToSpider s h m)
    (graft_spider_left_inverse s h m) (graft_spider_right_inverse s h m)
    (edge_graft_spider_left_inverse s h m) (edge_graft_spider_right_inverse s h m)
    (graft_spider_weights s h m f)

theorem zero_anchor_identification (s h m : Nat) (hs : 2 ≤ s) :
    spiderToGraft s h m (.arm ⟨0,by omega⟩ ⟨4*s-1,by omega⟩) =
      graftEmbed (boundaryCenter s) SpiderVertex.center (boundaryZero s) := by
  simp only [spiderToGraft,dite_true]
  have he : boundaryZero s = (leftVertex s ⟨4*s-1,by omega⟩).val := by
    apply Fin.ext; dsimp only [boundaryZero,leftVertex]; omega
  rw [he,embed_left]

theorem maximum_anchor_identification (s h m : Nat) :
    spiderToGraft s h m (.arm ⟨0,by omega⟩ ⟨4*s,by omega⟩) =
      graftEmbed (boundaryCenter s) SpiderVertex.center (boundaryMaximum s) := by
  simp only [spiderToGraft,dite_true]
  have he : boundaryMaximum s = (leftVertex s ⟨4*s,by omega⟩).val := by
    apply Fin.ext; dsimp only [boundaryMaximum,leftVertex]; omega
  rw [he,embed_left]

theorem uniform_first_arm_spiders (s h m : Nat) (hs : 2 ≤ s) :
    ∃ f : SpiderVertex (h+2) m (6*s+3) → Nat,
      Graceful (spiderGraph (h+2) m (6*s+3)) ((h+2)*(6*s+3)+m) f ∧
      f (.arm ⟨0,by omega⟩ ⟨4*s-1,by omega⟩)=0 ∧
      f (.arm ⟨0,by omega⟩ ⟨4*s,by omega⟩)=((h+2)*(6*s+3)+m) := by
  obtain ⟨f,hf,hzero,hmax⟩ := uniform_boundary_grafts s h m hs
  have hg := graft_graceful_on_spider s h m _ f hf
  have hm : 12*s+6+(h*(6*s+3)+m)=(h+2)*(6*s+3)+m := by
    simp only [Nat.add_mul]; omega
  rw [hm] at hg hmax
  refine ⟨fun v => f (spiderToGraft s h m v),hg,?_,?_⟩
  · dsimp only; rw [zero_anchor_identification s h m hs]; exact hzero
  · dsimp only; rw [maximum_anchor_identification s h m]; exact hmax

end GracefulBoundary

