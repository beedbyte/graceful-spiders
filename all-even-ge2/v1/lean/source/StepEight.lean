import GapGraph
namespace GracefulBoundary.FixedEven

@[simp] theorem fin8_val3 : (3:Fin 8).val=3 := rfl
@[simp] theorem fin8_val4 : (4:Fin 8).val=4 := rfl
@[simp] theorem fin8_val5 : (5:Fin 8).val=5 := rfl
@[simp] theorem fin8_val6 : (6:Fin 8).val=6 := rfl
@[simp] theorem fin8_val7 : (7:Fin 8).val=7 := rfl

def cut8 (n : Nat) := 4*n
def bridge8 (n : Nat) := 8*((n+1)/2)
def offsets8 (reverse : Bool) : List Nat := if reverse then [4,3,5,2,6,1,7,0] else [0,7,1,6,2,5,3,4]
def arm8 (n : Nat) (d : Fin 8) := cut8 n+1+(offsets8 (n%2≠0)).getD d.val 0

theorem offsets8_perm (reverse : Bool) : (offsets8 reverse).Perm (List.range 8) := by cases reverse <;> decide

theorem arm8_band (n : Nat) : BandBijection (arm8 n) (cut8 n+1) (cut8 n+8) := by
  have hp := (offsets8_perm (n%2≠0)).map (fun x => cut8 n+1+x)
  rw [←List.range'_eq_map_range] at hp
  have hb := list_band_bijection _ (cut8 n+1) (cut8 n+8) 8 (by omega) hp
  have eq : (fun d : Fin 8 => (List.map (fun x => cut8 n+1+x) (offsets8 (n%2≠0))).getD d.val 0)=arm8 n := by
    funext d
    have len : (offsets8 (n%2≠0)).length=8 := (offsets8_perm _).length_eq.trans (by decide)
    have hd : d.val<(offsets8 (n%2≠0)).length := by omega
    rw [←List.getElem_eq_getD (h:=by simpa only [List.length_map] using hd) 0,List.getElem_map]
    dsimp only [arm8]
    rw [List.getElem_eq_getD (h:=hd) 0]
  rw [eq] at hb; exact hb

theorem shifted_cuts (t k r x y : Nat) (hr : r≤k) : cuts (t+r) (shift t k x) (shift t k y) ↔ cuts t x y := by
  dsimp only [cuts,shift]
  repeat (any_goals (first | omega | split))

theorem gains_shift (k B C x : Nat) (hBC : B≤C ∧ C≤B+k) :
    gains k C (gapWeight k B x) ↔ gains k B x := by
  have mod := gapWeight_mod k B x
  dsimp only [gains,gapWeight] at *
  repeat (any_goals (first | omega | split at *))

def internal8 (n : Nat) (d : Fin 8) := if n%2=0 then 8-d.val else d.val

theorem arm8_actual_weights {V E : Type} (G : IndexedGraph V E) (root : V) (g : V → Nat)
    (n : Nat) (hn : 2≤n) (hroot : g root=1) (d : Fin 8) :
    weight (graph G root 8) (label g (cut8 n) 8 (arm8 n)) (.inr d)=
      if d.val=0 then bridge8 n else internal8 n d := by
  have hd : d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 ∨ d.val=4 ∨ d.val=5 ∨ d.val=6 ∨ d.val=7 := by omega
  rcases hd with hd|hd|hd|hd|hd|hd|hd|hd <;>
    rcases (show n%2=0 ∨ n%2=1 by omega) with hp|hp <;>
    simp only [weight,graph] <;>
    simp only [hd,ite_true] <;>
    simp_all [label,arm8,shift,cut8,bridge8,internal8,offsets8,distance] <;>
    (try dsimp only [Fin.instOfNat,Fin.ofNat]) <;> (try simp) <;>
    repeat (any_goals (first | omega | split))

theorem arm8_internal_cuts {V E : Type} (G : IndexedGraph V E) (root : V) (g : V → Nat)
    (n : Nat) (hn : 2≤n) (hroot : g root=1) (d : Fin 8) :
    cuts (cut8 (n+1))
      ((label g (cut8 n) 8 (arm8 n)) ((graph G root 8).source (.inr d)))
      ((label g (cut8 n) 8 (arm8 n)) ((graph G root 8).target (.inr d))) ↔
      (d.val≠0 ∨ n%2≠0) := by
  have hd : d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 ∨ d.val=4 ∨ d.val=5 ∨ d.val=6 ∨ d.val=7 := by omega
  rcases hd with hd|hd|hd|hd|hd|hd|hd|hd <;>
    rcases (show n%2=0 ∨ n%2=1 by omega) with hp|hp <;>
    simp only [graph] <;>
    simp only [hd,ite_true] <;>
    simp_all [label,arm8,shift,cut8,offsets8,cuts] <;>
    (try dsimp only [Fin.instOfNat,Fin.ofNat]) <;> (try simp) <;>
    repeat (any_goals (first | omega | split))

theorem arm8_weights {V E : Type} (G : IndexedGraph V E) (root : V) (g : V → Nat)
    (n : Nat) (hn : 2≤n) (hroot : g root=1) :
    ArmWeights 8 (bridge8 n) (fun d => weight (graph G root 8) (label g (cut8 n) 8 (arm8 n)) (.inr d)) := by
  have hB : 8≤bridge8 n := by dsimp only [bridge8]; omega
  constructor
  · intro d e he
    rw [arm8_actual_weights G root g n hn hroot d,arm8_actual_weights G root g n hn hroot e] at he
    apply Fin.ext
    have := d.isLt; have := e.isLt
    dsimp only [internal8] at he
    repeat (any_goals (first | omega | split at he))
  · intro d; rw [arm8_actual_weights G root g n hn hroot d]
    have := d.isLt
    dsimp only [internal8]
    repeat (any_goals (first | omega | split))
  · exact ⟨⟨0,by omega⟩,by rw [arm8_actual_weights G root g n hn hroot]; rfl⟩
  · intro x hx ht
    by_cases even : n%2=0
    · refine ⟨⟨8-x,by omega⟩,?_⟩
      rw [arm8_actual_weights G root g n hn hroot]
      dsimp only [internal8]
      rw [ite_eq_right (by omega),ite_eq_left even]
      omega
    · refine ⟨⟨x,ht⟩,?_⟩
      rw [arm8_actual_weights G root g n hn hroot]
      dsimp only [internal8]
      rw [ite_eq_right (by omega),ite_eq_right even]

theorem step8_graceful {V E : Type} (G : IndexedGraph V E) (root : V) (g : V → Nat)
    (n : Nat) (hn : 2≤n) (hg : Graceful G (8*n) g) (hroot : g root=1)
    (crossing : ∀e,cuts (cut8 n) (g (G.source e)) (g (G.target e)) ↔ gains 8 (bridge8 n) (weight G g e)) :
    Graceful (graph G root 8) (8*(n+1)) (label g (cut8 n) 8 (arm8 n)) := by
  have hB : 8≤bridge8 n ∧ bridge8 n≤8*n := by dsimp only [bridge8]; omega
  have hm : bridge8 n%8=0 := by simp only [bridge8,Nat.mul_mod_right]
  have hgraft := gap_graft G root g (8*n) 8 (cut8 n) (bridge8 n) hg (by omega) (by dsimp only [cut8]; omega) hB hm crossing (arm8 n) (arm8_band n) (arm8_weights G root g n hn hroot)
  simpa only [show 8*n+8=8*(n+1) by omega] using hgraft

theorem step8_crossing {V E : Type} (G : IndexedGraph V E) (root : V) (g : V → Nat)
    (n : Nat) (hn : 2≤n) (hroot : g root=1)
    (crossing : ∀e,cuts (cut8 n) (g (G.source e)) (g (G.target e)) ↔ gains 8 (bridge8 n) (weight G g e)) :
    ∀e,cuts (cut8 (n+1))
      ((label g (cut8 n) 8 (arm8 n)) ((graph G root 8).source e))
      ((label g (cut8 n) 8 (arm8 n)) ((graph G root 8).target e)) ↔
      gains 8 (bridge8 (n+1)) (weight (graph G root 8) (label g (cut8 n) 8 (arm8 n)) e) := by
  intro e; cases e with
  | inl e =>
    have hc : bridge8 n≤bridge8 (n+1) ∧ bridge8 (n+1)≤bridge8 n+8 := by dsimp only [bridge8]; omega
    have hw : weight (graph G root 8) (label g (cut8 n) 8 (arm8 n)) (.inl e)=gapWeight 8 (bridge8 n) (weight G g e) := by
      dsimp only [weight,graph,label]
      rw [shifted_distance]
      change (if cuts (cut8 n) (g (G.source e)) (g (G.target e)) then weight G g e+8 else weight G g e)=gapWeight 8 (bridge8 n) (weight G g e)
      simp only [gapWeight,←crossing e]
    rw [hw,gains_shift 8 _ _ _ hc]
    dsimp only [graph,label]
    rw [show cut8 (n+1)=cut8 n+4 by dsimp only [cut8]; omega,shifted_cuts _ 8 4 _ _ (by omega)]
    exact crossing e
  | inr d =>
    rw [arm8_internal_cuts G root g n hn hroot d,arm8_actual_weights G root g n hn hroot d]
    by_cases hd : d.val=0
    · rw [ite_eq_left hd]
      have hm : bridge8 n%8=0 := by simp only [bridge8,Nat.mul_mod_right]
      dsimp only [gains]
      rw [hm]
      dsimp only [bridge8]
      omega
    · rw [ite_eq_right hd]
      have hb : 1≤internal8 n d ∧ internal8 n d<8 := by
        have := d.isLt; dsimp only [internal8]; split <;> omega
      have hm := Nat.mod_eq_of_lt hb.2
      dsimp only [gains]
      rw [hm]
      omega

end GracefulBoundary.FixedEven
