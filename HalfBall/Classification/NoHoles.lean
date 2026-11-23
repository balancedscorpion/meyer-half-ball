module
public import HalfBall.Classification.Detection
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall
open MeyerGeneralProblem.LevOlevskii
open Set Metric Filter FourierTransform
open scoped Topology FourierTransform

/-- If a local atomic record with bounded site counts has a surviving
coefficient, its transform is nonzero on a compact test in every translate
of a fixed ball. Translating the test multiplies the isolated value by a
unit complex phase. -/
theorem no_holes_in_transform (p M : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ {T : TemperedDistribution (V p) ℂ} {E : Set (V p)}
      {a : E → ℂ}, BallCap E M →
      (∀ φ : SchwartzMap (V p) ℂ, HasCompactSupport φ → HasSum (fun z : E => a z * φ z) (T φ)) →
      (∃ x, a x ≠ 0) → ∀ c : V p, ∃ φ : SchwartzMap (V p) ℂ,
        Function.support φ ⊆ closedBall c R ∧ (𝓕 T) φ ≠ 0 := by
  obtain ⟨R,hR,hiso⟩ := isolated_window_of_ballCap p M
  refine ⟨R,hR,fun {T E a} hE hT ⟨x,hx⟩ c => ?_⟩
  obtain ⟨φ,hs,hφ,hz⟩ := hiso E hE x
  let ψ := SchwartzMap.compSubConstCLM ℂ c φ
  have hval (y : V p) : (𝓕 ψ) y = (frequencyPhase (-c) y : ℂ) * (𝓕 φ) y := by
    simpa [ψ] using fourier_test_add φ (-c) y
  refine ⟨ψ,?_,?_⟩
  · intro z hz
    change φ (z-c) ≠ 0 at hz
    simpa [dist_eq_norm] using hs hz
  · change T (𝓕 ψ) ≠ 0
    rw [evaluate_isolated_site hT x (𝓕 ψ) (fun y hy => by
      rw [hval,hz _ y.property (fun h => hy (Subtype.ext h)),mul_zero]),hval,hφ,mul_one]
    exact mul_ne_zero hx (Circle.coe_ne_zero _)

/-- Every nonempty spectral carrier meets every closed ball of a common
radius when the physical carrier has the given site cap and a nonzero
atom. No separation of the spectral sites is needed. -/
theorem spectral_carrier_relatively_dense {p M} {T : TemperedDistribution (V p) ℂ}
    {A B : Set (V p)} (hA : BallCap A M) (hT : LocalAtoms T A)
    (hν : LocalAtoms (𝓕 T) B) (ha : A.Nonempty) :
    ∃ R : ℝ, 0 < R ∧ ∀ c : V p, ∃ b ∈ B, dist c b ≤ R := by
  obtain ⟨R,hR,hwindow⟩ := no_holes_in_transform p M
  obtain ⟨a,ha0,hT⟩ := hT
  obtain ⟨b,_,hν⟩ := hν
  obtain ⟨x,hx⟩ := ha
  refine ⟨R,hR,fun c => ?_⟩
  obtain ⟨φ,hs,hn⟩ := hwindow hA hT ⟨⟨x,hx⟩,ha0 _⟩ c
  have hc : HasCompactSupport (φ : V p → ℂ) :=
    HasCompactSupport.intro (isCompact_closedBall _ _) fun z hz => by
      by_contra h; exact hz (hs h)
  by_contra! h
  have hz (i : B) : φ i = 0 := by
    by_contra hn
    exact (h i i.property).not_ge (dist_comm c i ▸ hs hn)
  exact hn (by simpa [hz] using (hν φ hc).tsum_eq.symm)

end HalfBall
