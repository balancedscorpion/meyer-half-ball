module

public import HalfBall.Poisson.Samples
public import HalfBall.Poisson.Summation
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Poisson

open MeasureTheory UnitAddTorus
open scoped InnerProductSpace ComplexConjugate FourierTransform

variable {p : ℕ}

def standard : Coordinates p ≃L[ℝ] V p := (PiLp.continuousLinearEquiv 2 ℝ _).symm

def physicalMap (L : LatticeCoset p) : V p ≃L[ℝ] V p := standard.symm.trans L.basis

def transpose (T : V p ≃L[ℝ] V p) : V p ≃L[ℝ] V p :=
  ContinuousLinearEquiv.equivOfInverse (ContinuousLinearMap.adjoint T.toContinuousLinearMap)
    (ContinuousLinearMap.adjoint T.symm.toContinuousLinearMap)
    (fun x => ext_inner_right ℝ fun y => by simp [ContinuousLinearMap.adjoint_inner_left])
    (fun x => ext_inner_right ℝ fun y => by simp [ContinuousLinearMap.adjoint_inner_left])

/-- The inverse transpose maps standard dual coordinates to spectral sites. -/
def reciprocalMap (L : LatticeCoset p) : V p ≃L[ℝ] V p := transpose (physicalMap L).symm

def reciprocal (L : LatticeCoset p) (v : V p) : LatticeCoset p :=
  ⟨v,standard.trans (reciprocalMap L)⟩

theorem reciprocal_pairing (L : LatticeCoset p) (u w : Coordinates p) :
    ⟪(reciprocal L 0).basis u,L.basis w⟫_ℝ = ∑ i, u i*w i := by
  change ⟪ContinuousLinearMap.adjoint (physicalMap L).symm.toContinuousLinearMap (standard u),
    (physicalMap L) (standard w)⟫_ℝ = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]
  simp [standard,PiLp.inner_apply,mul_comm]

/-- Jacobian for integration in reciprocal coordinates. -/
def jacobian (L : LatticeCoset p) : ℝ := |(LinearMap.det (reciprocalMap L).toLinearEquiv.toLinearMap)⁻¹|

theorem jacobian_pos (L : LatticeCoset p) : 0 < jacobian L :=
  abs_pos.mpr (inv_ne_zero (LinearEquiv.isUnit_det' _).ne_zero)

theorem reciprocal_integral (L : LatticeCoset p) (v : V p) (f : V p → ℂ) :
    (∫ u : Coordinates p, f (v+(reciprocal L 0).basis u)) = (jacobian L : ℂ) * ∫ x, f x := by
  let T := reciprocalMap L
  let g (x : V p) := f (v+x)
  have he := (PiLp.volume_preserving_toLp (Fin p)).integral_comp
    (MeasurableEquiv.toLp 2 (Coordinates p)).measurableEmbedding (fun z => g (T z))
  change (∫ u : Coordinates p, g (T (standard u))) = _
  rw [show (∫ u : Coordinates p, g (T (standard u))) = ∫ x, g (T x) from he]
  have hem := T.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map (μ := volume) g
  change (∫ x, g x ∂Measure.map T.toLinearEquiv.toLinearMap volume) = ∫ x, g (T x) at hem
  rw [← hem, Measure.map_linearMap_addHaar_eq_smul_addHaar volume (LinearEquiv.isUnit_det' _).ne_zero,
    integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]
  have htrans := (measurePreserving_add_left (volume : Measure (V p)) v).integral_comp
    (MeasurableEquiv.addLeft v).measurableEmbedding f
  simp only [g, htrans, jacobian, T, Complex.real_smul]

/-- The torus monomial agrees with the Euclidean Fourier character. -/
theorem monomial_eq_char (n : Indices p) (u : Coordinates p) :
    mFourier n (project u) = (Real.fourierChar (∑ i, (n i : ℝ)*u i) : ℂ) := by
  simp only [mFourier,ContinuousMap.coe_mk,project,fourier_coe_apply,Complex.ofReal_one,
    div_one,Real.fourierChar_apply,Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_intCast]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end HalfBall.Poisson
