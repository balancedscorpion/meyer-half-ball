module

public import Mathlib.Analysis.Distribution.TemperedDistribution
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

/-- Theorem A.3 (geometric local count). The same integer works in every open
unit ball. The centre ranges over all Euclidean space and sites on the
bounding hyperplane are included. -/
theorem geometric_local_count {p : ℕ} (hp : 0 < p) (B : Set (V p)) (η : V p) (S : ℕ → ℝ)
    (hB : LocallyFiniteSites B) (hη : ‖η‖ = 1)
    (hpatch : OrderedPatchBound B) (hS : HalfBallCount B η S) :
    ∃ M : ℕ, ∀ y : V p, ((B ∩ halfSpace η) ∩ Metric.ball y 1).ncard ≤ M := by
  sorry

noncomputable section
open scoped FourierTransform

/-- The locally finite carrier lists exactly the nonzero atoms on compactly supported
Schwartz tests. Temperedness is a property of the distribution. -/
def LocalAtoms {p} (μ : TemperedDistribution (V p) ℂ) (A : Set (V p)) : Prop :=
  ∃ a : A → ℂ, (∀ x, a x ≠ 0) ∧ ∀ φ : SchwartzMap (V p) ℂ, HasCompactSupport φ →
    HasSum (fun x : A => a x * φ x) (μ φ)

/-- The physical and spectral directions and radius sequences are independent. -/
def IndependentHalfBallData {p} (A B : Set (V p)) : Prop :=
  ∃ (ω η : V p) (R S : ℕ → ℝ), ‖ω‖ = 1 ∧ ‖η‖ = 1 ∧ HalfBallCount A ω R ∧ HalfBallCount B η S

structure LatticeCoset (p : ℕ) where
  shift : V p
  basis : (Fin p → ℝ) ≃L[ℝ] V p

def LatticeCoset.site {p : ℕ} (L : LatticeCoset p) (z : Fin p → ℤ) : V p :=
  L.shift + L.basis (fun k => (z k : ℝ))

def Poisson.phase (r : ℝ) : ℂ := Real.fourierChar r

/-- Equality on all Schwartz tests with a finite sum of full-rank lattice combs.
Each term has its own lattice, shift, modulation and complex coefficient. -/
def WeightedLatticeCombs {p : ℕ} (μ : TemperedDistribution (V p) ℂ) : Prop :=
  ∃ (m : ℕ) (L : Fin m → LatticeCoset p) (v : Fin m → V p) (c : Fin m → ℂ),
    ∀ φ : SchwartzMap (V p) ℂ, μ φ =
      ∑ i, c i * ∑' n, Poisson.phase ⟪v i,(L i).site n⟫_ℝ * φ ((L i).site n)

/-- Theorem 1.1 for a locally finite, locally atomic Fourier pair.
The two half-ball directions and the two sequences of radii are independent. -/
theorem half_ball_theorem_iff {p} (hp : 0 < p) {μ : TemperedDistribution (V p) ℂ} {A B : Set (V p)}
    (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B)
    (ha : LocalAtoms μ A) (hb : LocalAtoms (𝓕 μ) B) :
    IndependentHalfBallData A B ↔ WeightedLatticeCombs μ := by
  sorry

end
end HalfBall
