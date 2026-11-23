module

public import HalfBall.Statement
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Order.Zorn
import Mathlib.Tactic

public section
namespace HalfBall
open Set Metric

private theorem maximal_separated_class {p} (E : Set (V p)) :
    ∃ F ⊆ E, F.Pairwise (fun x y => 1 ≤ dist x y) ∧
      ∀ x ∈ E, ∃ y ∈ F, dist y x < 1 := by
  let choices := {F : Set (V p) | F ⊆ E ∧ F.Pairwise (fun x y => 1 ≤ dist x y)}
  obtain ⟨F,hF⟩ := zorn_subset choices fun c hc hchain =>
    ⟨⋃₀ c, ⟨sUnion_subset fun _ h => (hc h).1,
      hchain.pairwise_sUnion.mpr fun _ h => (hc h).2⟩,
      fun _ h => subset_sUnion_of_mem h⟩
  refine ⟨F,hF.prop.1,hF.prop.2,fun x hx => ?_⟩
  by_contra! h
  have hxF : x ∉ F := fun hmem => by have hh := h x hmem; rw [dist_self] at hh; linarith
  have hi : insert x F ∈ choices := ⟨insert_subset hx hF.prop.1,
    pairwise_insert.mpr ⟨hF.prop.2,fun y hy _ => ⟨dist_comm y x ▸ h y hy,h y hy⟩⟩⟩
  exact hxF (hF.le_of_ge hi (subset_insert ..) (mem_insert ..))

private theorem separated_classes_at_sites {p M} {E : Set (V p)}
    (h : ∀ x ∈ E, ∀ T : Finset (V p), (T : Set _) ⊆ E ∩ ball x 1 → T.card ≤ M) :
    ∃ F : Fin M → Set (V p), E = ⋃ i, F i ∧ ∀ i, (F i).Pairwise (fun x y => 1 ≤ dist x y) := by
  classical
  induction M generalizing E with
  | zero =>
    refine ⟨Fin.elim0,?_,fun i => i.elim0⟩
    ext x
    simp only [iUnion_of_empty,mem_empty_iff_false,iff_false]
    intro hx
    have hh := h x hx {x} (by simpa using And.intro hx (mem_ball_self zero_lt_one : x ∈ ball x 1))
    simp at hh
  | succ m ih =>
    obtain ⟨F,hFE,hsep,hnear⟩ := maximal_separated_class E
    obtain ⟨G,hG,hsepG⟩ := ih (E := E \ F) (by
      intro x hx T hT
      obtain ⟨y,hy,hyx⟩ := hnear x hx.1
      have hny : y ∉ T := fun hmem => (hT hmem).1.2 hy
      have hi := h x hx.1 (insert y T) (by
        rw [Finset.coe_insert]
        exact insert_subset ⟨hFE hy,hyx⟩ (fun z hz => ⟨(hT hz).1.1,(hT hz).2⟩))
      rw [Finset.card_insert_of_notMem hny] at hi
      omega)
    refine ⟨Fin.cons F G,?_,Fin.cases hsep hsepG⟩
    ext x
    constructor
    · intro hx
      by_cases hxF : x ∈ F
      · exact mem_iUnion.mpr ⟨0, hxF⟩
      · obtain ⟨i,hi⟩ := mem_iUnion.mp (hG ▸ (show x ∈ E \ F from ⟨hx,hxF⟩))
        exact mem_iUnion.mpr ⟨i.succ,hi⟩
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      refine Fin.cases (fun h0 => hFE h0) (fun j hj => ?_) i hi
      have hxG : x ∈ ⋃ k, G k := mem_iUnion.mpr ⟨j,hj⟩
      rw [← hG] at hxG
      exact hxG.1

/-- The colouring step of B.1. A unit-ball cap of M gives M classes with
pairwise distances at least one within each class, however close points of
different classes are. Removing a maximal separated class reduces the
count in every unit ball centred on a remaining site. -/
theorem separated_classes_of_ballCap {p M} {E : Set (V p)} (h : BallCap E M) :
    ∃ F : Fin M → Set (V p), E = ⋃ i, F i ∧ ∀ i, (F i).Pairwise (fun x y => 1 ≤ dist x y) :=
  separated_classes_at_sites (fun x _ => h x)

end HalfBall
