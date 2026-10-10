import Q54Certificates
namespace GracefulBoundary.Q54

def DepthZero (n m d : Nat) (a : Fin n) : Prop :=
  ∃ (hlt : d-1<71) (f : SpiderVertex n m 71 → Nat),
    Graceful (spiderGraph n m 71) (71*n+m) f ∧
    f (.arm a ⟨d-1,hlt⟩)=0

/-- Exactly four interior depths on every actual named S(71^n,1^m). -/
theorem selected_actual (n m d : Nat) (hn : 2≤n) (a : Fin n)
    (hd : d=65 ∨ d=66 ∨ d=67 ∨ d=68) : DepthZero n m d a := by
  rcases hd with h|h|h|h
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 66 65 n m
      (coreLabels 142 output_C8) packet_C8 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 66 65 n m
      (coreLabels 142 output_C8) packet_C8 hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 66 67 n m
      (coreLabels 142 output_C7) packet_C7 hn a).2
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩
  · subst d
    obtain ⟨f,hf,hz⟩ := (FiniteAlpha.prescribed_zero 34 68 69 n m
      (coreLabels 142 output_older) packet_older hn a).1
    exact ⟨by decide,f,by simpa [Nat.mul_comm] using hf,hz⟩

end GracefulBoundary.Q54
