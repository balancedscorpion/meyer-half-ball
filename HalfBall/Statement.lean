module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

namespace HalfBall

open Filter MeasureTheory
open scoped InnerProductSpace

abbrev V (p : ℕ) := EuclideanSpace ℝ (Fin p)

def LocallyFiniteSites {p} (B : Set (V p)) : Prop :=
  ∀ K : Set (V p), IsCompact K → (B ∩ K).Finite

def halfSpace {p} (η : V p) : Set (V p) := {s | 0 ≤ ⟪η, s⟫_ℝ}

def halfBall {p} (η : V p) (R : ℝ) : Set (V p) :=
  halfSpace η ∩ Metric.closedBall 0 R

/-- Finite unions of closed axis-parallel boxes, with positive Lebesgue volume. -/
def IsPatch {p} (E : Set (V p)) : Prop :=
  (∃ (n : ℕ) (lo hi : Fin n → Fin p → ℝ),
    E = ⋃ i, {x | ∀ k, x k ∈ Set.Icc (lo i k) (hi i k)}) ∧ 0 < volume E

def differencesAt {p} (s : V p) (E F : Set (V p)) : Set (V p) :=
  Set.image2 (fun x y => s + x - y) E F

def OrderedPatchBound {p} (B : Set (V p)) : Prop :=
  ∃ a : ℝ, 0 ≤ a ∧ ∀ s ∈ B, ∀ (n : ℕ) (E : Fin n → Set (V p)),
    (∀ i, IsPatch (E i)) →
    (∀ i, differencesAt s (E i) (E i) ∩ B = {s}) →
    (∀ i k, k < i → differencesAt s (E i) (E k) ∩ B = ∅) →
    ∑ i, volume (E i) ≤ ENNReal.ofReal a

def HalfBallCount {p} (B : Set (V p)) (η : V p) (S : ℕ → ℝ) : Prop :=
  (∀ j, 0 < S j) ∧ Tendsto S atTop atTop ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ j in atTop, ((B ∩ halfBall η (S j)).ncard : ℝ) ≤ C * S j ^ p

/-- Bounds on finite subfamilies count distinct sites and make sense for any set. -/
def BallCap {p} (B : Set (V p)) (M : ℕ) : Prop :=
  ∀ (y : V p) (T : Finset (V p)), (↑T : Set (V p)) ⊆ B ∩ Metric.ball y 1 → T.card ≤ M

/-- The statement of Theorem A.3, manuscript pp. 19–22. -/
def GeometricLocalCount : Prop :=
  ∀ (p : ℕ), 0 < p → ∀ (B : Set (V p)) (η : V p) (S : ℕ → ℝ),
    LocallyFiniteSites B → ‖η‖ = 1 → OrderedPatchBound B → HalfBallCount B η S →
    ∃ M : ℕ, BallCap (B ∩ halfSpace η) M

end HalfBall
