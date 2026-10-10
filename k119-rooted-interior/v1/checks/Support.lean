import K119Through118
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Audit
open GracefulBoundary GracefulBoundary.Rooted71
def triangle : IndexedGraph (Fin 3) (Fin 3) where
  source := fun e => e
  target := fun e => if e.val=0 then ⟨1,by decide⟩ else if e.val=1 then ⟨2,by decide⟩ else ⟨0,by decide⟩
def triangleLabel (v : Fin 3) : Nat := if v.val=0 then 0 else if v.val=1 then 1 else 3
theorem triangleGraceful : ConventionalGraceful triangle 3 triangleLabel := by
  refine ⟨⟨by decide,by decide⟩,⟨by decide,by decide,?_⟩⟩
  intro x hx htop
  have split : x=1 ∨ x=2 ∨ x=3 := by omega
  rcases split with rfl|rfl|rfl
  · exact ⟨⟨0,by decide⟩,rfl⟩
  · exact ⟨⟨1,by decide⟩,rfl⟩
  · exact ⟨⟨2,by decide⟩,rfl⟩
theorem triangleRoot : triangleLabel ⟨0,by decide⟩=0 := rfl
theorem triangleNotOnto : ¬ Graceful triangle 3 triangleLabel := by
  intro h
  obtain ⟨v,hv⟩ := h.vertices.onto 2 (by decide) (by decide)
  have avoid : ∀ v : Fin 3, triangleLabel v ≠ 2 := by decide
  exact avoid v hv
def singleton : IndexedGraph (Fin 1) Empty where
  source := Empty.elim
  target := Empty.elim
def singletonLabel (_ : Fin 1) : Nat := 0
theorem singletonGraceful : ConventionalGraceful singleton 0 singletonLabel := by
  refine ⟨⟨by decide,by decide⟩,⟨?_,?_,?_⟩⟩
  · intro e; cases e
  · intro e e'; cases e
  · intro x hx ht; omega
def edge : IndexedGraph (Fin 2) (Fin 1) where
  source := fun _ => ⟨0,by decide⟩
  target := fun _ => ⟨1,by decide⟩
def edgeLabel (v : Fin 2) := v.val
theorem edgeGraceful : ConventionalGraceful edge 1 edgeLabel := by
  refine ⟨⟨by decide,by decide⟩,⟨by decide,by decide,?_⟩⟩
  intro x hx ht
  have : x=1 := by omega
  subst x
  exact ⟨⟨0,by decide⟩,rfl⟩

def disconnected : IndexedGraph (Fin 5) (Fin 6) where
  source := fun e => if e.val<3 then ⟨0,by decide⟩ else if e.val<5 then ⟨1,by decide⟩ else ⟨2,by decide⟩
  target := fun e => if e.val=0 then ⟨1,by decide⟩ else if e.val=1 ∨ e.val=3 then ⟨2,by decide⟩ else ⟨3,by decide⟩
def disconnectedLabel (v : Fin 5) : Nat :=
  if v.val=0 then 0 else if v.val=1 then 1 else if v.val=2 then 4 else if v.val=3 then 6 else 2
theorem disconnectedGraceful : ConventionalGraceful disconnected 6 disconnectedLabel := by
  refine ⟨⟨by decide,by decide⟩,⟨by decide,by decide,?_⟩⟩
  intro x hx htop
  have finiteOnto : ∀ i : Fin 6, ∃ e : Fin 6, weight disconnected disconnectedLabel e=i.val+1 := by decide
  obtain ⟨e,he⟩ := finiteOnto ⟨x-1,by omega⟩
  exact ⟨e,by simpa only [show x-1+1=x by omega] using he⟩
theorem disconnectedNotOnto : ¬Graceful disconnected 6 disconnectedLabel := by
  intro h
  obtain ⟨v,hv⟩ := h.vertices.onto 3 (by decide) (by decide)
  have avoid : ∀ v : Fin 5, disconnectedLabel v ≠3 := by decide
  exact avoid v hv
theorem isolated_vertex : ∀ e : Fin 6,
  disconnected.source e≠⟨4,by decide⟩ ∧ disconnected.target e≠⟨4,by decide⟩ := by decide
theorem explicit_triangle_cycle :
  disconnected.source ⟨0,by decide⟩=⟨0,by decide⟩ ∧ disconnected.target ⟨0,by decide⟩=⟨1,by decide⟩ ∧
  disconnected.source ⟨3,by decide⟩=⟨1,by decide⟩ ∧ disconnected.target ⟨3,by decide⟩=⟨2,by decide⟩ ∧
  disconnected.source ⟨1,by decide⟩=⟨0,by decide⟩ ∧ disconnected.target ⟨1,by decide⟩=⟨2,by decide⟩ := by decide


end Audit
