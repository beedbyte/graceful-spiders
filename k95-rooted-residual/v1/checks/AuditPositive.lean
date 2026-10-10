import K95Rooted
namespace ReplayAudit
open GracefulBoundary GracefulBoundary.Rooted71

theorem exact_interior {W F : Type} (H : IndexedGraph W F) (root : W)
    (g : W → Nat) (Q d : Nat) (hg : ConventionalGraceful H Q g)
    (hroot : g root=0) (hd : 1≤d ∧ d≤94) :
    (∃ f : GraftVertices (Fin 191) W (⟨95,by decide⟩ : Fin 191) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 190) H (⟨95,by decide⟩ : Fin 191) root) (190+Q) f ∧
      f (graftEmbed (⟨95,by decide⟩ : Fin 191) root (⟨95-d,by omega⟩ : Fin 191))=0) ∧
    (∃ f : GraftVertices (Fin 191) W (⟨95,by decide⟩ : Fin 191) → Nat,
      ConventionalGraceful (graftGraph (pathGraph 190) H (⟨95,by decide⟩ : Fin 191) root) (190+Q) f ∧
      f (graftEmbed (⟨95,by decide⟩ : Fin 191) root (⟨95+d,by omega⟩ : Fin 191))=0) :=
  K95Rooted.interior H root g Q d hg hroot hd

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
theorem triangle_all_depths (d : Nat) (hd : 1≤d ∧ d≤94) :
    Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-d,by omega⟩ ∧
    Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+d,by omega⟩ :=
  K95Rooted.interior triangle ⟨0,by decide⟩ triangleLabel 3 d triangleGraceful triangleRoot hd

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
theorem tri_left_1 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-1,by decide⟩ := (triangle_all_depths 1 (by decide)).1
theorem tri_right_1 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+1,by decide⟩ := (triangle_all_depths 1 (by decide)).2
theorem tri_left_2 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-2,by decide⟩ := (triangle_all_depths 2 (by decide)).1
theorem tri_right_2 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+2,by decide⟩ := (triangle_all_depths 2 (by decide)).2
theorem tri_left_3 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-3,by decide⟩ := (triangle_all_depths 3 (by decide)).1
theorem tri_right_3 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+3,by decide⟩ := (triangle_all_depths 3 (by decide)).2
theorem tri_left_4 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-4,by decide⟩ := (triangle_all_depths 4 (by decide)).1
theorem tri_right_4 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+4,by decide⟩ := (triangle_all_depths 4 (by decide)).2
theorem tri_left_5 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-5,by decide⟩ := (triangle_all_depths 5 (by decide)).1
theorem tri_right_5 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+5,by decide⟩ := (triangle_all_depths 5 (by decide)).2
theorem tri_left_6 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-6,by decide⟩ := (triangle_all_depths 6 (by decide)).1
theorem tri_right_6 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+6,by decide⟩ := (triangle_all_depths 6 (by decide)).2
theorem tri_left_7 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-7,by decide⟩ := (triangle_all_depths 7 (by decide)).1
theorem tri_right_7 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+7,by decide⟩ := (triangle_all_depths 7 (by decide)).2
theorem tri_left_8 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-8,by decide⟩ := (triangle_all_depths 8 (by decide)).1
theorem tri_right_8 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+8,by decide⟩ := (triangle_all_depths 8 (by decide)).2
theorem tri_left_9 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-9,by decide⟩ := (triangle_all_depths 9 (by decide)).1
theorem tri_right_9 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+9,by decide⟩ := (triangle_all_depths 9 (by decide)).2
theorem tri_left_10 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-10,by decide⟩ := (triangle_all_depths 10 (by decide)).1
theorem tri_right_10 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+10,by decide⟩ := (triangle_all_depths 10 (by decide)).2
theorem tri_left_11 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-11,by decide⟩ := (triangle_all_depths 11 (by decide)).1
theorem tri_right_11 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+11,by decide⟩ := (triangle_all_depths 11 (by decide)).2
theorem tri_left_12 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-12,by decide⟩ := (triangle_all_depths 12 (by decide)).1
theorem tri_right_12 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+12,by decide⟩ := (triangle_all_depths 12 (by decide)).2
theorem tri_left_13 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-13,by decide⟩ := (triangle_all_depths 13 (by decide)).1
theorem tri_right_13 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+13,by decide⟩ := (triangle_all_depths 13 (by decide)).2
theorem tri_left_14 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-14,by decide⟩ := (triangle_all_depths 14 (by decide)).1
theorem tri_right_14 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+14,by decide⟩ := (triangle_all_depths 14 (by decide)).2
theorem tri_left_15 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-15,by decide⟩ := (triangle_all_depths 15 (by decide)).1
theorem tri_right_15 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+15,by decide⟩ := (triangle_all_depths 15 (by decide)).2
theorem tri_left_16 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-16,by decide⟩ := (triangle_all_depths 16 (by decide)).1
theorem tri_right_16 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+16,by decide⟩ := (triangle_all_depths 16 (by decide)).2
theorem tri_left_17 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-17,by decide⟩ := (triangle_all_depths 17 (by decide)).1
theorem tri_right_17 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+17,by decide⟩ := (triangle_all_depths 17 (by decide)).2
theorem tri_left_18 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-18,by decide⟩ := (triangle_all_depths 18 (by decide)).1
theorem tri_right_18 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+18,by decide⟩ := (triangle_all_depths 18 (by decide)).2
theorem tri_left_19 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-19,by decide⟩ := (triangle_all_depths 19 (by decide)).1
theorem tri_right_19 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+19,by decide⟩ := (triangle_all_depths 19 (by decide)).2
theorem tri_left_20 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-20,by decide⟩ := (triangle_all_depths 20 (by decide)).1
theorem tri_right_20 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+20,by decide⟩ := (triangle_all_depths 20 (by decide)).2
theorem tri_left_21 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-21,by decide⟩ := (triangle_all_depths 21 (by decide)).1
theorem tri_right_21 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+21,by decide⟩ := (triangle_all_depths 21 (by decide)).2
theorem tri_left_22 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-22,by decide⟩ := (triangle_all_depths 22 (by decide)).1
theorem tri_right_22 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+22,by decide⟩ := (triangle_all_depths 22 (by decide)).2
theorem tri_left_23 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-23,by decide⟩ := (triangle_all_depths 23 (by decide)).1
theorem tri_right_23 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+23,by decide⟩ := (triangle_all_depths 23 (by decide)).2
theorem tri_left_24 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-24,by decide⟩ := (triangle_all_depths 24 (by decide)).1
theorem tri_right_24 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+24,by decide⟩ := (triangle_all_depths 24 (by decide)).2
theorem tri_left_25 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-25,by decide⟩ := (triangle_all_depths 25 (by decide)).1
theorem tri_right_25 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+25,by decide⟩ := (triangle_all_depths 25 (by decide)).2
theorem tri_left_26 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-26,by decide⟩ := (triangle_all_depths 26 (by decide)).1
theorem tri_right_26 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+26,by decide⟩ := (triangle_all_depths 26 (by decide)).2
theorem tri_left_27 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-27,by decide⟩ := (triangle_all_depths 27 (by decide)).1
theorem tri_right_27 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+27,by decide⟩ := (triangle_all_depths 27 (by decide)).2
theorem tri_left_28 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-28,by decide⟩ := (triangle_all_depths 28 (by decide)).1
theorem tri_right_28 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+28,by decide⟩ := (triangle_all_depths 28 (by decide)).2
theorem tri_left_29 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-29,by decide⟩ := (triangle_all_depths 29 (by decide)).1
theorem tri_right_29 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+29,by decide⟩ := (triangle_all_depths 29 (by decide)).2
theorem tri_left_30 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-30,by decide⟩ := (triangle_all_depths 30 (by decide)).1
theorem tri_right_30 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+30,by decide⟩ := (triangle_all_depths 30 (by decide)).2
theorem tri_left_31 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-31,by decide⟩ := (triangle_all_depths 31 (by decide)).1
theorem tri_right_31 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+31,by decide⟩ := (triangle_all_depths 31 (by decide)).2
theorem tri_left_32 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-32,by decide⟩ := (triangle_all_depths 32 (by decide)).1
theorem tri_right_32 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+32,by decide⟩ := (triangle_all_depths 32 (by decide)).2
theorem tri_left_33 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-33,by decide⟩ := (triangle_all_depths 33 (by decide)).1
theorem tri_right_33 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+33,by decide⟩ := (triangle_all_depths 33 (by decide)).2
theorem tri_left_34 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-34,by decide⟩ := (triangle_all_depths 34 (by decide)).1
theorem tri_right_34 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+34,by decide⟩ := (triangle_all_depths 34 (by decide)).2
theorem tri_left_35 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-35,by decide⟩ := (triangle_all_depths 35 (by decide)).1
theorem tri_right_35 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+35,by decide⟩ := (triangle_all_depths 35 (by decide)).2
theorem tri_left_36 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-36,by decide⟩ := (triangle_all_depths 36 (by decide)).1
theorem tri_right_36 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+36,by decide⟩ := (triangle_all_depths 36 (by decide)).2
theorem tri_left_37 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-37,by decide⟩ := (triangle_all_depths 37 (by decide)).1
theorem tri_right_37 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+37,by decide⟩ := (triangle_all_depths 37 (by decide)).2
theorem tri_left_38 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-38,by decide⟩ := (triangle_all_depths 38 (by decide)).1
theorem tri_right_38 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+38,by decide⟩ := (triangle_all_depths 38 (by decide)).2
theorem tri_left_39 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-39,by decide⟩ := (triangle_all_depths 39 (by decide)).1
theorem tri_right_39 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+39,by decide⟩ := (triangle_all_depths 39 (by decide)).2
theorem tri_left_40 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-40,by decide⟩ := (triangle_all_depths 40 (by decide)).1
theorem tri_right_40 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+40,by decide⟩ := (triangle_all_depths 40 (by decide)).2
theorem tri_left_41 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-41,by decide⟩ := (triangle_all_depths 41 (by decide)).1
theorem tri_right_41 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+41,by decide⟩ := (triangle_all_depths 41 (by decide)).2
theorem tri_left_42 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-42,by decide⟩ := (triangle_all_depths 42 (by decide)).1
theorem tri_right_42 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+42,by decide⟩ := (triangle_all_depths 42 (by decide)).2
theorem tri_left_43 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-43,by decide⟩ := (triangle_all_depths 43 (by decide)).1
theorem tri_right_43 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+43,by decide⟩ := (triangle_all_depths 43 (by decide)).2
theorem tri_left_44 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-44,by decide⟩ := (triangle_all_depths 44 (by decide)).1
theorem tri_right_44 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+44,by decide⟩ := (triangle_all_depths 44 (by decide)).2
theorem tri_left_45 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-45,by decide⟩ := (triangle_all_depths 45 (by decide)).1
theorem tri_right_45 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+45,by decide⟩ := (triangle_all_depths 45 (by decide)).2
theorem tri_left_46 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-46,by decide⟩ := (triangle_all_depths 46 (by decide)).1
theorem tri_right_46 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+46,by decide⟩ := (triangle_all_depths 46 (by decide)).2
theorem tri_left_47 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-47,by decide⟩ := (triangle_all_depths 47 (by decide)).1
theorem tri_right_47 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+47,by decide⟩ := (triangle_all_depths 47 (by decide)).2
theorem tri_left_48 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-48,by decide⟩ := (triangle_all_depths 48 (by decide)).1
theorem tri_right_48 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+48,by decide⟩ := (triangle_all_depths 48 (by decide)).2
theorem tri_left_49 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-49,by decide⟩ := (triangle_all_depths 49 (by decide)).1
theorem tri_right_49 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+49,by decide⟩ := (triangle_all_depths 49 (by decide)).2
theorem tri_left_50 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-50,by decide⟩ := (triangle_all_depths 50 (by decide)).1
theorem tri_right_50 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+50,by decide⟩ := (triangle_all_depths 50 (by decide)).2
theorem tri_left_51 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-51,by decide⟩ := (triangle_all_depths 51 (by decide)).1
theorem tri_right_51 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+51,by decide⟩ := (triangle_all_depths 51 (by decide)).2
theorem tri_left_52 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-52,by decide⟩ := (triangle_all_depths 52 (by decide)).1
theorem tri_right_52 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+52,by decide⟩ := (triangle_all_depths 52 (by decide)).2
theorem tri_left_53 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-53,by decide⟩ := (triangle_all_depths 53 (by decide)).1
theorem tri_right_53 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+53,by decide⟩ := (triangle_all_depths 53 (by decide)).2
theorem tri_left_54 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-54,by decide⟩ := (triangle_all_depths 54 (by decide)).1
theorem tri_right_54 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+54,by decide⟩ := (triangle_all_depths 54 (by decide)).2
theorem tri_left_55 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-55,by decide⟩ := (triangle_all_depths 55 (by decide)).1
theorem tri_right_55 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+55,by decide⟩ := (triangle_all_depths 55 (by decide)).2
theorem tri_left_56 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-56,by decide⟩ := (triangle_all_depths 56 (by decide)).1
theorem tri_right_56 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+56,by decide⟩ := (triangle_all_depths 56 (by decide)).2
theorem tri_left_57 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-57,by decide⟩ := (triangle_all_depths 57 (by decide)).1
theorem tri_right_57 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+57,by decide⟩ := (triangle_all_depths 57 (by decide)).2
theorem tri_left_58 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-58,by decide⟩ := (triangle_all_depths 58 (by decide)).1
theorem tri_right_58 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+58,by decide⟩ := (triangle_all_depths 58 (by decide)).2
theorem tri_left_59 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-59,by decide⟩ := (triangle_all_depths 59 (by decide)).1
theorem tri_right_59 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+59,by decide⟩ := (triangle_all_depths 59 (by decide)).2
theorem tri_left_60 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-60,by decide⟩ := (triangle_all_depths 60 (by decide)).1
theorem tri_right_60 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+60,by decide⟩ := (triangle_all_depths 60 (by decide)).2
theorem tri_left_61 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-61,by decide⟩ := (triangle_all_depths 61 (by decide)).1
theorem tri_right_61 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+61,by decide⟩ := (triangle_all_depths 61 (by decide)).2
theorem tri_left_62 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-62,by decide⟩ := (triangle_all_depths 62 (by decide)).1
theorem tri_right_62 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+62,by decide⟩ := (triangle_all_depths 62 (by decide)).2
theorem tri_left_63 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-63,by decide⟩ := (triangle_all_depths 63 (by decide)).1
theorem tri_right_63 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+63,by decide⟩ := (triangle_all_depths 63 (by decide)).2
theorem tri_left_64 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-64,by decide⟩ := (triangle_all_depths 64 (by decide)).1
theorem tri_right_64 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+64,by decide⟩ := (triangle_all_depths 64 (by decide)).2
theorem tri_left_65 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-65,by decide⟩ := (triangle_all_depths 65 (by decide)).1
theorem tri_right_65 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+65,by decide⟩ := (triangle_all_depths 65 (by decide)).2
theorem tri_left_66 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-66,by decide⟩ := (triangle_all_depths 66 (by decide)).1
theorem tri_right_66 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+66,by decide⟩ := (triangle_all_depths 66 (by decide)).2
theorem tri_left_67 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-67,by decide⟩ := (triangle_all_depths 67 (by decide)).1
theorem tri_right_67 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+67,by decide⟩ := (triangle_all_depths 67 (by decide)).2
theorem tri_left_68 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-68,by decide⟩ := (triangle_all_depths 68 (by decide)).1
theorem tri_right_68 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+68,by decide⟩ := (triangle_all_depths 68 (by decide)).2
theorem tri_left_69 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-69,by decide⟩ := (triangle_all_depths 69 (by decide)).1
theorem tri_right_69 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+69,by decide⟩ := (triangle_all_depths 69 (by decide)).2
theorem tri_left_70 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-70,by decide⟩ := (triangle_all_depths 70 (by decide)).1
theorem tri_right_70 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+70,by decide⟩ := (triangle_all_depths 70 (by decide)).2
theorem tri_left_71 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-71,by decide⟩ := (triangle_all_depths 71 (by decide)).1
theorem tri_right_71 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+71,by decide⟩ := (triangle_all_depths 71 (by decide)).2
theorem tri_left_72 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-72,by decide⟩ := (triangle_all_depths 72 (by decide)).1
theorem tri_right_72 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+72,by decide⟩ := (triangle_all_depths 72 (by decide)).2
theorem tri_left_73 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-73,by decide⟩ := (triangle_all_depths 73 (by decide)).1
theorem tri_right_73 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+73,by decide⟩ := (triangle_all_depths 73 (by decide)).2
theorem tri_left_74 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-74,by decide⟩ := (triangle_all_depths 74 (by decide)).1
theorem tri_right_74 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+74,by decide⟩ := (triangle_all_depths 74 (by decide)).2
theorem tri_left_75 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-75,by decide⟩ := (triangle_all_depths 75 (by decide)).1
theorem tri_right_75 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+75,by decide⟩ := (triangle_all_depths 75 (by decide)).2
theorem tri_left_76 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-76,by decide⟩ := (triangle_all_depths 76 (by decide)).1
theorem tri_right_76 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+76,by decide⟩ := (triangle_all_depths 76 (by decide)).2
theorem tri_left_77 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-77,by decide⟩ := (triangle_all_depths 77 (by decide)).1
theorem tri_right_77 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+77,by decide⟩ := (triangle_all_depths 77 (by decide)).2
theorem tri_left_78 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-78,by decide⟩ := (triangle_all_depths 78 (by decide)).1
theorem tri_right_78 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+78,by decide⟩ := (triangle_all_depths 78 (by decide)).2
theorem tri_left_79 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-79,by decide⟩ := (triangle_all_depths 79 (by decide)).1
theorem tri_right_79 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+79,by decide⟩ := (triangle_all_depths 79 (by decide)).2
theorem tri_left_80 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-80,by decide⟩ := (triangle_all_depths 80 (by decide)).1
theorem tri_right_80 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+80,by decide⟩ := (triangle_all_depths 80 (by decide)).2
theorem tri_left_81 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-81,by decide⟩ := (triangle_all_depths 81 (by decide)).1
theorem tri_right_81 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+81,by decide⟩ := (triangle_all_depths 81 (by decide)).2
theorem tri_left_82 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-82,by decide⟩ := (triangle_all_depths 82 (by decide)).1
theorem tri_right_82 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+82,by decide⟩ := (triangle_all_depths 82 (by decide)).2
theorem tri_left_83 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-83,by decide⟩ := (triangle_all_depths 83 (by decide)).1
theorem tri_right_83 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+83,by decide⟩ := (triangle_all_depths 83 (by decide)).2
theorem tri_left_84 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-84,by decide⟩ := (triangle_all_depths 84 (by decide)).1
theorem tri_right_84 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+84,by decide⟩ := (triangle_all_depths 84 (by decide)).2
theorem tri_left_85 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-85,by decide⟩ := (triangle_all_depths 85 (by decide)).1
theorem tri_right_85 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+85,by decide⟩ := (triangle_all_depths 85 (by decide)).2
theorem tri_left_86 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-86,by decide⟩ := (triangle_all_depths 86 (by decide)).1
theorem tri_right_86 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+86,by decide⟩ := (triangle_all_depths 86 (by decide)).2
theorem tri_left_87 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-87,by decide⟩ := (triangle_all_depths 87 (by decide)).1
theorem tri_right_87 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+87,by decide⟩ := (triangle_all_depths 87 (by decide)).2
theorem tri_left_88 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-88,by decide⟩ := (triangle_all_depths 88 (by decide)).1
theorem tri_right_88 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+88,by decide⟩ := (triangle_all_depths 88 (by decide)).2
theorem tri_left_89 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-89,by decide⟩ := (triangle_all_depths 89 (by decide)).1
theorem tri_right_89 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+89,by decide⟩ := (triangle_all_depths 89 (by decide)).2
theorem tri_left_90 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-90,by decide⟩ := (triangle_all_depths 90 (by decide)).1
theorem tri_right_90 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+90,by decide⟩ := (triangle_all_depths 90 (by decide)).2
theorem tri_left_91 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-91,by decide⟩ := (triangle_all_depths 91 (by decide)).1
theorem tri_right_91 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+91,by decide⟩ := (triangle_all_depths 91 (by decide)).2
theorem tri_left_92 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-92,by decide⟩ := (triangle_all_depths 92 (by decide)).1
theorem tri_right_92 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+92,by decide⟩ := (triangle_all_depths 92 (by decide)).2
theorem tri_left_93 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-93,by decide⟩ := (triangle_all_depths 93 (by decide)).1
theorem tri_right_93 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+93,by decide⟩ := (triangle_all_depths 93 (by decide)).2
theorem tri_left_94 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95-94,by decide⟩ := (triangle_all_depths 94 (by decide)).1
theorem tri_right_94 : Q24Rooted.ZeroAt triangle ⟨0,by decide⟩ 3 46 ⟨95+94,by decide⟩ := (triangle_all_depths 94 (by decide)).2
theorem singleton_left_1 : Q24Rooted.ZeroAt singleton ⟨0,by decide⟩ 0 46 ⟨95-1,by decide⟩ := (K95Rooted.interior singleton ⟨0,by decide⟩ singletonLabel 0 1 singletonGraceful rfl (by decide)).1
theorem singleton_right_1 : Q24Rooted.ZeroAt singleton ⟨0,by decide⟩ 0 46 ⟨95+1,by decide⟩ := (K95Rooted.interior singleton ⟨0,by decide⟩ singletonLabel 0 1 singletonGraceful rfl (by decide)).2
theorem singleton_left_94 : Q24Rooted.ZeroAt singleton ⟨0,by decide⟩ 0 46 ⟨95-94,by decide⟩ := (K95Rooted.interior singleton ⟨0,by decide⟩ singletonLabel 0 94 singletonGraceful rfl (by decide)).1
theorem singleton_right_94 : Q24Rooted.ZeroAt singleton ⟨0,by decide⟩ 0 46 ⟨95+94,by decide⟩ := (K95Rooted.interior singleton ⟨0,by decide⟩ singletonLabel 0 94 singletonGraceful rfl (by decide)).2
theorem edge_left_1 : Q24Rooted.ZeroAt edge ⟨0,by decide⟩ 1 46 ⟨95-1,by decide⟩ := (K95Rooted.interior edge ⟨0,by decide⟩ edgeLabel 1 1 edgeGraceful rfl (by decide)).1
theorem edge_right_1 : Q24Rooted.ZeroAt edge ⟨0,by decide⟩ 1 46 ⟨95+1,by decide⟩ := (K95Rooted.interior edge ⟨0,by decide⟩ edgeLabel 1 1 edgeGraceful rfl (by decide)).2
theorem edge_left_94 : Q24Rooted.ZeroAt edge ⟨0,by decide⟩ 1 46 ⟨95-94,by decide⟩ := (K95Rooted.interior edge ⟨0,by decide⟩ edgeLabel 1 94 edgeGraceful rfl (by decide)).1
theorem edge_right_94 : Q24Rooted.ZeroAt edge ⟨0,by decide⟩ 1 46 ⟨95+94,by decide⟩ := (K95Rooted.interior edge ⟨0,by decide⟩ edgeLabel 1 94 edgeGraceful rfl (by decide)).2

#print GracefulBoundary.K95Rooted.interior
#print axioms GracefulBoundary.K95Rooted.interior
end ReplayAudit
