import ThirdSpider
namespace GracefulBoundary.Variable

def boundaryCenter (p : Nat) : Fin (4*p+7) := ⟨2*p+3,by omega⟩
abbrev BoundaryGraftVertex (p h m : Nat) :=
  GraftVertices (Fin (4*p+7)) (SpiderVertex h m (2*p+3)) (boundaryCenter p)
noncomputable def boundaryGraftGraph (p h m : Nat) :=
  graftGraph (pathGraph (4*p+6)) (spiderGraph h m (2*p+3)) (boundaryCenter p) SpiderVertex.center
def boundaryGraftLabel (p h m : Nat) (c : List Nat) : BoundaryGraftVertex p h m → Nat :=
  graftLabel (boundaryCenter p) (pathLabel (4*p+6) c) (residualLabel h m (2*p+3))
    (2*p+2) (h*(2*p+3)+m)

def leftVertex (p : Nat) (d : Fin (2*p+3)) : {v : Fin (4*p+7) // v ≠ boundaryCenter p} :=
  ⟨⟨2*p+2-d.val,by omega⟩,by intro he; have := congrArg Fin.val he; simp only [boundaryCenter] at this; omega⟩
def rightVertex (p : Nat) (d : Fin (2*p+3)) : {v : Fin (4*p+7) // v ≠ boundaryCenter p} :=
  ⟨⟨2*p+4+d.val,by omega⟩,by intro he; have := congrArg Fin.val he; simp only [boundaryCenter] at this; omega⟩

def spiderToGraft (p h m : Nat) : SpiderVertex (h+2) m (2*p+3) → BoundaryGraftVertex p h m
  | .center => .inr .center
  | .leaf j => .inr (.leaf j)
  | .arm i d => if h0 : i.val=0 then .inl (leftVertex p d)
    else if h1 : i.val=1 then .inl (rightVertex p d)
    else .inr (.arm ⟨i.val-2,by omega⟩ d)

def graftToSpider (p h m : Nat) : BoundaryGraftVertex p h m → SpiderVertex (h+2) m (2*p+3)
  | .inr .center => .center
  | .inr (.leaf j) => .leaf j
  | .inr (.arm i d) => .arm ⟨i.val+2,by omega⟩ d
  | .inl v => if hv : v.val.val < 2*p+3 then
      .arm ⟨0,by omega⟩ ⟨2*p+2-v.val.val,by omega⟩
    else .arm ⟨1,by omega⟩ ⟨v.val.val-(2*p+4),by have := v.val.isLt; omega⟩

theorem graftToSpider_left (p h m : Nat) (d : Fin (2*p+3)) :
    graftToSpider p h m (.inl (leftVertex p d)) = .arm ⟨0,by omega⟩ d := by
  dsimp only [graftToSpider,leftVertex]
  rw [dite_eq_left (by omega)]
  congr 1
  apply Fin.ext
  dsimp only
  omega

theorem graftToSpider_right (p h m : Nat) (d : Fin (2*p+3)) :
    graftToSpider p h m (.inl (rightVertex p d)) = .arm ⟨1,by omega⟩ d := by
  dsimp only [graftToSpider,rightVertex]
  rw [dite_eq_right (by omega)]
  congr 1
  apply Fin.ext
  dsimp only
  omega

theorem graft_spider_left_inverse (p h m : Nat) (v : SpiderVertex (h+2) m (2*p+3)) :
    graftToSpider p h m (spiderToGraft p h m v)=v := by
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

theorem graft_spider_right_inverse (p h m : Nat) (v : BoundaryGraftVertex p h m) :
    spiderToGraft p h m (graftToSpider p h m v)=v := by
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
    have hn : v.val.val ≠ 2*p+3 := by
      intro he; apply v.property; apply Fin.ext; exact he
    simp only [graftToSpider]
    split
    · simp only [spiderToGraft,dite_true]
      congr 1; apply Subtype.ext; apply Fin.ext
      simp only [leftVertex]; omega
    · simp only [spiderToGraft,show (1:Nat)≠0 by omega,dite_false,dite_true]
      congr 1; apply Subtype.ext; apply Fin.ext
      simp only [rightVertex]; omega

abbrev BoundaryGraftEdge (p h m : Nat) := Sum (Fin (4*p+6)) (SpiderEdge h m (2*p+3))
def spiderEdgeToGraft (p h m : Nat) : SpiderEdge (h+2) m (2*p+3) → BoundaryGraftEdge p h m
  | .leaf j => .inr (.leaf j)
  | .arm i d => if h0 : i.val=0 then .inl ⟨2*p+2-d.val,by omega⟩
    else if h1 : i.val=1 then .inl ⟨2*p+3+d.val,by omega⟩
    else .inr (.arm ⟨i.val-2,by omega⟩ d)
def graftEdgeToSpider (p h m : Nat) : BoundaryGraftEdge p h m → SpiderEdge (h+2) m (2*p+3)
  | .inr (.leaf j) => .leaf j
  | .inr (.arm i d) => .arm ⟨i.val+2,by omega⟩ d
  | .inl e => if he : e.val < 2*p+3 then .arm ⟨0,by omega⟩ ⟨2*p+2-e.val,by omega⟩
    else .arm ⟨1,by omega⟩ ⟨e.val-(2*p+3),by omega⟩

theorem edge_graft_spider_left_inverse (p h m : Nat) (e : SpiderEdge (h+2) m (2*p+3)) :
    graftEdgeToSpider p h m (spiderEdgeToGraft p h m e)=e := by
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

theorem edge_graft_spider_right_inverse (p h m : Nat) (e : BoundaryGraftEdge p h m) :
    spiderEdgeToGraft p h m (graftEdgeToSpider p h m e)=e := by
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




theorem embed_left (p h m : Nat) (d : Fin (2*p+3)) :
    graftEmbed (boundaryCenter p) (SpiderVertex.center : SpiderVertex h m (2*p+3))
      (leftVertex p d).val = Sum.inl (leftVertex p d) := by
  simp only [graftEmbed,dite_eq_right (leftVertex p d).property]

theorem embed_right (p h m : Nat) (d : Fin (2*p+3)) :
    graftEmbed (boundaryCenter p) (SpiderVertex.center : SpiderVertex h m (2*p+3))
      (rightVertex p d).val = Sum.inl (rightVertex p d) := by
  simp only [graftEmbed,dite_eq_right (rightVertex p d).property]

theorem graft_spider_weights (p h m : Nat) (f : BoundaryGraftVertex p h m → Nat)
    (e : SpiderEdge (h+2) m (2*p+3)) :
    weight (spiderGraph (h+2) m (2*p+3)) (fun v => f (spiderToGraft p h m v)) e =
      weight (boundaryGraftGraph p h m) f (spiderEdgeToGraft p h m e) := by
  classical
  cases e with
  | leaf j => rfl
  | arm i d =>
    by_cases h0 : i.val=0
    · have ht : spiderToGraft p h m (.arm i d) =
          (boundaryGraftGraph p h m).source (spiderEdgeToGraft p h m (.arm i d)) := by
        simp only [spiderToGraft,spiderEdgeToGraft,dite_eq_left h0,boundaryGraftGraph,graftGraph,pathGraph]
        exact (embed_left p h m d).symm
      have hs : spiderToGraft p h m ((spiderGraph (h+2) m (2*p+3)).source (.arm i d)) =
          (boundaryGraftGraph p h m).target (spiderEdgeToGraft p h m (.arm i d)) := by
        simp only [spiderEdgeToGraft,dite_eq_left h0,boundaryGraftGraph,graftGraph,pathGraph,spiderGraph]
        by_cases hd : d.val=0
        · rw [ite_eq_left hd]
          have he : (⟨2*p+2-d.val+1,by omega⟩ : Fin (4*p+7))=boundaryCenter p := by
            apply Fin.ext; dsimp only [boundaryCenter]; omega
          rw [he]
          simp only [spiderToGraft,graftEmbed,dite_true]
        · rw [ite_eq_right hd]
          simp only [spiderToGraft,dite_eq_left h0]
          have he : (⟨2*p+2-d.val+1,by omega⟩ : Fin (4*p+7))=
              (leftVertex p ⟨d.val-1,by omega⟩).val := by
            apply Fin.ext; dsimp only [leftVertex]; omega
          rw [he,embed_left]
      change distance (f (spiderToGraft p h m ((spiderGraph (h+2) m (2*p+3)).source (.arm i d))))
        (f (spiderToGraft p h m (.arm i d))) = _
      rw [hs,ht]
      exact distance_comm _ _
    · by_cases h1 : i.val=1
      · have ht : spiderToGraft p h m (.arm i d) =
            (boundaryGraftGraph p h m).target (spiderEdgeToGraft p h m (.arm i d)) := by
          simp only [spiderToGraft,spiderEdgeToGraft,dite_eq_right h0,dite_eq_left h1,boundaryGraftGraph,graftGraph,pathGraph]
          have he : (⟨2*p+3+d.val+1,by omega⟩ : Fin (4*p+7))=(rightVertex p d).val := by
            apply Fin.ext; dsimp only [rightVertex]; omega
          rw [he,embed_right]
        have hs : spiderToGraft p h m ((spiderGraph (h+2) m (2*p+3)).source (.arm i d)) =
            (boundaryGraftGraph p h m).source (spiderEdgeToGraft p h m (.arm i d)) := by
          simp only [spiderEdgeToGraft,dite_eq_right h0,dite_eq_left h1,boundaryGraftGraph,graftGraph,pathGraph,spiderGraph]
          by_cases hd : d.val=0
          · rw [ite_eq_left hd]
            have he : (⟨2*p+3+d.val,by omega⟩ : Fin (4*p+7))=boundaryCenter p := by
              apply Fin.ext; dsimp only [boundaryCenter]; omega
            rw [he]
            simp only [spiderToGraft,graftEmbed,dite_true]
          · rw [ite_eq_right hd]
            simp only [spiderToGraft,dite_eq_right h0,dite_eq_left h1]
            have he : (⟨2*p+3+d.val,by omega⟩ : Fin (4*p+7))=
                (rightVertex p ⟨d.val-1,by omega⟩).val := by
              apply Fin.ext; dsimp only [rightVertex]; omega
            rw [he,embed_right]
        change distance (f (spiderToGraft p h m ((spiderGraph (h+2) m (2*p+3)).source (.arm i d))))
          (f (spiderToGraft p h m (.arm i d))) = _
        rw [hs,ht]
        rfl
      · by_cases hd : d.val=0 <;>
          simp only [weight,spiderGraph,spiderEdgeToGraft,dite_eq_right h0,dite_eq_right h1,
            boundaryGraftGraph,graftGraph,spiderToGraft,hd,ite_true,ite_false]




theorem graft_graceful_on_spider (p h m M : Nat) (f : BoundaryGraftVertex p h m → Nat)
    (hf : Graceful (boundaryGraftGraph p h m) M f) :
    Graceful (spiderGraph (h+2) m (2*p+3)) M (fun v => f (spiderToGraft p h m v)) :=
  graceful_transport (boundaryGraftGraph p h m) (spiderGraph (h+2) m (2*p+3)) M f hf
    (spiderToGraft p h m) (graftToSpider p h m) (spiderEdgeToGraft p h m) (graftEdgeToSpider p h m)
    (graft_spider_left_inverse p h m) (graft_spider_right_inverse p h m)
    (edge_graft_spider_left_inverse p h m) (edge_graft_spider_right_inverse p h m)
    (graft_spider_weights p h m f)


end GracefulBoundary.Variable
