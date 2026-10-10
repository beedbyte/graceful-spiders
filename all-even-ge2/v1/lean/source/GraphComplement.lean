import ThreeDepthTheorem
namespace GracefulBoundary

def complementLabel {V : Type} (N : Nat) (f : V → Nat) : V → Nat := fun v => N-f v

theorem complement_band {V : Type} (N : Nat) (f : V → Nat) (hf : BandBijection f 0 N) :
    BandBijection (complementLabel N f) 0 N := by
  constructor
  · intro v; dsimp [complementLabel]; omega
  · intro v w eq
    have hv := hf.bounds v; have hw := hf.bounds w
    apply hf.injective v w
    dsimp [complementLabel] at eq; omega
  · intro x _ hx
    obtain ⟨v,hv⟩ := hf.onto (N-x) (by omega) (by omega)
    exact ⟨v,by dsimp [complementLabel]; omega⟩

theorem complement_involution {V : Type} (N : Nat) (f : V → Nat) (hf : BandBijection f 0 N) :
    complementLabel N (complementLabel N f)=f := by
  funext v; have hv := hf.bounds v; dsimp [complementLabel]; omega

theorem complement_weight {V E : Type} (G : IndexedGraph V E) (N : Nat) (f : V → Nat)
    (hf : BandBijection f 0 N) (e : E) : weight G (complementLabel N f) e=weight G f e := by
  exact complement_difference N _ _ (hf.bounds (G.source e)).2 (hf.bounds (G.target e)).2

/-- Complements every vertex of the supplied actual graph; each edge keeps its own weight. -/
theorem whole_graph_graceful_complement {V E : Type} (G : IndexedGraph V E) (N : Nat) (f : V → Nat)
    (hf : Graceful G N f) : Graceful G N (complementLabel N f) := by
  refine ⟨complement_band N f hf.vertices,?_⟩
  have eq : weight G (complementLabel N f)=weight G f := by funext e; exact complement_weight G N f hf.vertices e
  rw [eq]; exact hf.edges

theorem complement_maximum_zero {V : Type} (N : Nat) (f : V → Nat) (v : V) (hv : f v=N) :
    complementLabel N f v=0 := by simp [complementLabel,hv]

end GracefulBoundary
