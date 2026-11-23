module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

namespace HalfBall

open Filter MeasureTheory
open scoped InnerProductSpace

/-- Real p-dimensional Euclidean space with its standard Lebesgue measure. -/
abbrev V (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- Every compact set contains finitely many sites. -/
def LocallyFiniteSites {p} (B : Set (V p)) : Prop :=
  ∀ K : Set (V p), IsCompact K → (B ∩ K).Finite

/-- Closed half-space with inward normal η and boundary through zero. -/
def halfSpace {p} (η : V p) : Set (V p) := {s | 0 ≤ ⟪η, s⟫_ℝ}

/-- Origin-centred closed ball intersected with the closed measured half-space. -/
def halfBall {p} (η : V p) (R : ℝ) : Set (V p) :=
  halfSpace η ∩ Metric.closedBall 0 R

/-- Finite unions of closed axis-parallel boxes, with positive Lebesgue volume. -/
def IsPatch {p} (E : Set (V p)) : Prop :=
  (∃ (n : ℕ) (lo hi : Fin n → Fin p → ℝ),
    E = ⋃ i, {x | ∀ k, x k ∈ Set.Icc (lo i k) (hi i k)}) ∧ 0 < volume E

/-- Displacements from the second patch to the first, translated by s. -/
def differencesAt {p} (s : V p) (E F : Set (V p)) : Set (V p) :=
  Set.image2 (fun x y => s + x - y) E F

/-- One finite real bounds total patch volume at every anchor. Only later-to-earlier
patch differences must avoid the carrier. -/
def OrderedPatchBound {p} (B : Set (V p)) : Prop :=
  ∃ a : ℝ, 0 ≤ a ∧ ∀ s ∈ B, ∀ (n : ℕ) (E : Fin n → Set (V p)),
    (∀ i, IsPatch (E i)) →
    (∀ i, differencesAt s (E i) (E i) ∩ B = {s}) →
    (∀ i k, k < i → differencesAt s (E i) (E k) ∩ B = ∅) →
    ∑ i, volume (E i) ≤ ENNReal.ofReal a

/-- A sequence of positive radii tending to infinity with eventually O(S^p) sites. -/
def HalfBallCount {p} (B : Set (V p)) (η : V p) (S : ℕ → ℝ) : Prop :=
  (∀ j, 0 < S j) ∧ Tendsto S atTop atTop ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ j in atTop, ((B ∩ halfBall η (S j)).ncard : ℝ) ≤ C * S j ^ p

/-- Bounds on finite subfamilies count distinct sites and make sense for any set. -/
def BallCap {p} (B : Set (V p)) (M : ℕ) : Prop :=
  ∀ (y : V p) (T : Finset (V p)), (↑T : Set (V p)) ⊆ B ∩ Metric.ball y 1 → T.card ≤ M

end HalfBall
