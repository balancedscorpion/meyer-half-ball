module

public import HalfBall.Fourier.PhysicalRank
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Fourier

open MeasureTheory Filter Set
open scoped Topology ContDiff

variable {p : ℕ}

/-- Derivatives of order l cost at most a factor R^l under dilation. -/
theorem deriv_sample_le (h : SchwartzMap (V p) ℂ) {R : ℝ} (hR : 0 < R) (q x : V p) (l : ℕ) :
    ‖iteratedFDeriv ℝ l (sample h R hR q) x‖ ≤
      ‖iteratedFDeriv ℝ l h (R • (x-q))‖ * R^l := by
  let D : V p →L[ℝ] V p := R • ContinuousLinearMap.id ℝ _
  have hD : ‖D‖ ≤ R := by
    dsimp [D]; rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hR.le).trans_eq (mul_one _)
  change ‖iteratedFDeriv ℝ l (fun z => (h ∘ D) (z-q)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub, D.iteratedFDeriv_comp_right (h.smooth l) _ (by simp)]
  refine ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hD _) (norm_nonneg _)

/-- Away from a unit neighborhood of its centre, every weighted derivative
of the dilated kernel decays faster than any prescribed power of R,
uniformly over bounded centres. -/
theorem weighted_deriv_sample_le (h : SchwartzMap (V p) ℂ) {Q : ℝ} (hQ : 0 ≤ Q) (k l N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ} (hR : 1 ≤ R) (q x : V p), ‖q‖ ≤ Q → 1 ≤ ‖x-q‖ →
      R^N * ‖x‖^k * ‖iteratedFDeriv ℝ l (sample h R (by linarith) q) x‖ ≤ C := by
  let m := k+(N+l)
  let C := SchwartzMap.seminorm ℂ m l h
  refine ⟨(1+Q)^k * C, mul_nonneg (by positivity) (apply_nonneg _ _), ?_⟩
  intro R hR q x hq hx
  have hpos : 0 < R := by linarith
  let u := ‖x-q‖
  have hxx : ‖x‖ ≤ (1+Q)*u := by
    have ht := norm_le_norm_add_norm_sub q x
    change 1 ≤ u at hx
    dsimp [u] at *
    nlinarith [mul_nonneg hQ (sub_nonneg.mpr hx),norm_sub_rev q x]
  let d := ‖iteratedFDeriv ℝ l h (R • (x-q))‖
  have hd := SchwartzMap.le_seminorm ℂ m l h (R • (x-q))
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hpos] at hd
  change (R*u)^m * d ≤ C at hd
  have huu : 1 ≤ u^(N+l) := one_le_pow₀ hx
  have hrr : 1 ≤ R^k := one_le_pow₀ hR
  have haux : R^(N+l)*u^k ≤ (R*u)^m := by
    calc
      _ ≤ (R^(N+l)*u^k)*(R^k*u^(N+l)) :=
        le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hrr huu)
      _ = _ := by dsimp [m]; rw [mul_pow, pow_add R, pow_add u]; ring
  calc R^N * ‖x‖^k * ‖iteratedFDeriv ℝ l (sample h R hpos q) x‖
      ≤ R^N * ((1+Q)*u)^k * (d*R^l) := by
        gcongr
        exact deriv_sample_le h hpos q x l
    _ = (1+Q)^k * ((R^(N+l)*u^k)*d) := by rw [mul_pow,pow_add]; ring
    _ ≤ (1+Q)^k * ((R*u)^m*d) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

end HalfBall.Fourier
