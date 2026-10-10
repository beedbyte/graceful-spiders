import ReverseTracking

namespace GracefulBoundary.ReverseComplement

theorem selected_gadget_signatures :
    Variable.pre .g4=[3,6] ∧ Variable.before .g4=[9,4] ∧
    Variable.after .g4=[1,1,2,5,3,2,4,6,5,7,7,8,8,9] ∧
    Variable.pre .g6=[3,5,6,6] ∧ Variable.before .g6=[9,4] ∧
    Variable.after .g6=[1,1,2,5,4,2,3,7,7,8,8,9] ∧
    (Variable.pre .g4).length=2 ∧ (Variable.pre .g6).length=4 := by decide

theorem seed16_tracks : TrackedCore 16 16 5 Compatible.C16_16 := by
  refine ⟨Compatible.C16_16_valid,?_,?_,?_⟩ <;> decide

theorem seed17_tracks : TrackedCore 17 22 7 Compatible.C17_22 := by
  refine ⟨Compatible.C17_22_valid,?_,?_,?_⟩ <;> decide

theorem seed18_tracks : TrackedCore 18 22 9 Compatible.C18_22 := by
  refine ⟨Compatible.C18_22_valid,?_,?_,?_⟩ <;> decide

theorem seed19_tracks : TrackedCore 19 20 11 Compatible.C19_20 := by
  refine ⟨Compatible.C19_20_valid,?_,?_,?_⟩ <;> decide

theorem seed20_tracks : TrackedCore 20 24 15 Compatible.C20_24 := by
  refine ⟨Compatible.C20_24_valid,?_,?_,?_⟩ <;> decide

theorem seed21_tracks : TrackedCore 21 22 14 Compatible.C21_22 := by
  refine ⟨Compatible.C21_22_valid,?_,?_,?_⟩ <;> decide

theorem residue_seed (p : Nat) (hp : 16≤p ∧ p≤21) :
    ∃ b,(24≤b ∧ b≤27) ∧ Source p b := by
  have sizes : p=16 ∨ p=17 ∨ p=18 ∨ p=19 ∨ p=20 ∨ p=21 := by omega
  rcases sizes with rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨26,by decide,16,5,Compatible.C16_16,seed16_tracks,by decide⟩
  · exact ⟨26,by decide,22,7,Compatible.C17_22,seed17_tracks,by decide⟩
  · exact ⟨26,by decide,22,9,Compatible.C18_22,seed18_tracks,by decide⟩
  · exact ⟨26,by decide,20,11,Compatible.C19_20,seed19_tracks,by decide⟩
  · exact ⟨24,by decide,24,15,Compatible.C20_24,seed20_tracks,by decide⟩
  · exact ⟨27,by decide,22,14,Compatible.C21_22,seed21_tracks,by decide⟩

theorem common_residue_interval (p j d : Nat) (hp : 16+9*j≤p)
    (hl : 27+14*j≤d) (hu : d≤25+16*j) : AllOdd.Coverage p d := by
  obtain ⟨p0,r,hp0,size⟩ := Compatible.residue_selection p j hp
  obtain ⟨b,hb,seed⟩ := residue_seed p0 hp0
  have core := source_interval_coverage p0 b seed j d (by omega) (by omega)
  have final := AllOdd.coverage_grow (p0+9*j) d core r
  rw [size] at final
  exact final

end GracefulBoundary.ReverseComplement
