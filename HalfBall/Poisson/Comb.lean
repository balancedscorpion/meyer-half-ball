module

public import HalfBall.Poisson.DualLattice
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Poisson

open MeasureTheory UnitAddTorus FourierTransform
open scoped FourierTransform InnerProductSpace

variable {p : ℕ}

def phase (r : ℝ) : ℂ := Real.fourierChar r

@[simp] theorem phase_add (a b : ℝ) : phase (a+b) = phase a * phase b := by
  simp [phase,AddChar.map_add_eq_mul]

@[simp] theorem norm_phase (a : ℝ) : ‖phase a‖ = 1 := Circle.norm_coe _

/-- The compact test on reciprocal coordinates used to compute the transform. -/
private def test (L : LatticeCoset p) (v : V p) (φ : SchwartzMap (V p) ℂ) (u : Coordinates p) :=
  let x := v + (reciprocal L 0).basis u
  phase (-⟪x,L.shift⟫_ℝ) * φ x

private theorem coefficient (L : LatticeCoset p) (v : V p) (φ : SchwartzMap (V p) ℂ)
    (n : Indices p) :
    (∫ u, mFourier (-n) (project u) * test L v φ u) =
      (jacobian L : ℂ) * (phase ⟪v,L.basis (grid n)⟫_ℝ * (𝓕 φ) (L.site n)) := by
  let b := L.basis (grid n)
  let d := (reciprocal L 0).basis
  let f (x : V p) := phase (-⟪x,L.site n⟫_ℝ) * φ x
  have hfreq (u : Coordinates p) : mFourier (-n) (project u) = phase (-⟪d u,b⟫_ℝ) := by
    rw [monomial_eq_char]
    change phase _ = _
    congr 1
    rw [show ⟪d u,b⟫_ℝ = _ from reciprocal_pairing L u (grid n)]
    simp [grid,Finset.sum_neg_distrib,mul_comm]
  have hcalc (u : Coordinates p) :
      mFourier (-n) (project u) * test L v φ u = phase ⟪v,b⟫_ℝ * f (v+d u) := by
    rw [hfreq]
    change _ * (phase _ * _) = _ * (phase _ * _)
    rw [← mul_assoc, ← mul_assoc, ← phase_add, ← phase_add]
    congr 2
    change -⟪d u,b⟫_ℝ + -⟪v+d u,L.shift⟫_ℝ = ⟪v,b⟫_ℝ + -⟪v+d u,L.shift+b⟫_ℝ
    simp [inner_add_left,inner_add_right]
    ring
  simp_rw [hcalc]
  rw [integral_const_mul,reciprocal_integral]
  have hFourier : (∫ x, f x) = (𝓕 φ) (L.site n) := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    rfl
  rw [hFourier]
  ring

theorem summable_modulated (L : LatticeCoset p) (v : V p) (φ : SchwartzMap (V p) ℂ) :
    Summable (fun n : Indices p => phase ⟪v,L.site n⟫_ℝ * φ (L.site n)) := by
  apply Summable.of_norm
  simpa only [norm_mul,norm_phase,one_mul] using summable_lattice_samples L φ

/-- Poisson summation for one translated, modulated full-rank lattice comb.
The Jacobian is positive; the right side displays every reciprocal lattice
site, the phase from the physical translation, and the modulation shift. -/
theorem comb_poisson (L : LatticeCoset p) (v : V p) (φ : SchwartzMap (V p) ℂ)
    (hc : HasCompactSupport φ) :
    (jacobian L : ℂ) * (∑' n, phase ⟪v,L.site n⟫_ℝ * (𝓕 φ) (L.site n)) =
    phase ⟪v,L.shift⟫_ℝ * ∑' k, phase (-⟪(reciprocal L v).site k,L.shift⟫_ℝ) *
      φ ((reciprocal L v).site k) := by
  let d := (reciprocal L 0).basis
  let e := d.toHomeomorph.trans (Homeomorph.addLeft v)
  have hcont : Continuous (test L v φ) := by
    have hp : Continuous phase := continuous_subtype_val.comp Real.continuous_fourierChar
    exact (hp.comp ((e.continuous.inner continuous_const).neg)).mul (φ.continuous.comp e.continuous)
  have hcompact : HasCompactSupport (test L v φ) := (hc.comp_homeomorph e).mul_left
  let a (n : Indices p) := phase ⟪v,L.basis (grid n)⟫_ℝ * (𝓕 φ) (L.site n)
  have hsum : Summable a := by
    apply Summable.of_norm
    simpa [a] using summable_lattice_samples L (𝓕 φ)
  have hcoef := coefficient L v φ
  have h := (poisson_compact hcont hcompact (by simp_rw [hcoef]; exact hsum.mul_left _) 0).tsum_eq
  have hzero (n : Indices p) : mFourier n (project (0 : Coordinates p)) = 1 := by
    simp [monomial_eq_char, AddChar.map_zero_eq_one]
  simp_rw [hcoef,hzero,mul_one,zero_add] at h
  have hp (n : Indices p) : phase ⟪v,L.site n⟫_ℝ * (𝓕 φ) (L.site n) =
      phase ⟪v,L.shift⟫_ℝ * a n := by
    change phase ⟪v,L.shift+L.basis (grid n)⟫_ℝ * _ = _ * (_ * _)
    rw [inner_add_right,phase_add,mul_assoc]
  simp_rw [hp]
  rw [tsum_mul_left, mul_left_comm, ← tsum_mul_left]
  exact congrArg (phase ⟪v,L.shift⟫_ℝ * ·) h

end HalfBall.Poisson
