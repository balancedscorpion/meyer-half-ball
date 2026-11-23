module

public import HalfBall.FourierCarriers
public import HalfBall.Poisson.Comb
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Fourier

open Filter MeasureTheory Set FourierTransform
open scoped InnerProductSpace FourierTransform
open Poisson (phase)

variable {p : ℕ}

/-- A spectral Schwartz test at frequency q and scale R, with physical
transform supported in the measured half-ball when the cutoff is so supported. -/
def sample (h : SchwartzMap (V p) ℂ) (R : ℝ) (hR : 0 < R) (q : V p) : SchwartzMap (V p) ℂ :=
  (SchwartzMap.compSubConstCLM ℂ q) ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne') : V p ≃L[ℝ] V p)) h)

@[simp] theorem sample_apply (h : SchwartzMap (V p) ℂ) {R : ℝ} (hR : 0 < R) (q z : V p) :
    sample h R hR q z = h (R • (z-q)) := rfl

theorem fourier_sample (h : SchwartzMap (V p) ℂ) {R : ℝ} (hR : 0 < R) (q x : V p) :
    (𝓕 (sample h R hR q)) x = phase (-⟪q,x⟫_ℝ) * ((R^p : ℝ)⁻¹ : ℂ) * (𝓕 h) (R⁻¹ • x) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  let f (y : V p) := phase (-⟪y,R⁻¹ • x⟫_ℝ) * h y
  let g (z : V p) := phase (-⟪z,x⟫_ℝ) * sample h R hR q z
  change ∫ z, g z = _
  have hshift := integral_add_right_eq_self g q (μ := volume)
  rw [← hshift]
  have hval (z : V p) : g (z+q) = phase (-⟪q,x⟫_ℝ) * f (R • z) := by
    simp [g,f,inner_add_left,real_inner_smul_left,real_inner_smul_right,
      ← mul_assoc,hR.ne']
  simp_rw [hval]
  rw [integral_const_mul,volume.integral_comp_smul_of_nonneg f R (hR := hR.le)]
  have he : (∫ y, f y) = (𝓕 h) (R⁻¹ • x) := rfl
  rw [he]
  simp [Complex.real_smul,mul_assoc]

theorem support_fourier_sample {h : SchwartzMap (V p) ℂ} {ω : V p}
    (hs : Function.support (𝓕 h : SchwartzMap (V p) ℂ) ⊆ halfBall ω 1)
    {R : ℝ} (hR : 0 < R) (q : V p) :
    Function.support (𝓕 (sample h R hR q) : SchwartzMap (V p) ℂ) ⊆ halfBall ω R := by
  intro x hx
  have hnon : (𝓕 h) (R⁻¹ • x) ≠ 0 := by
    intro hz; apply hx; simp [fourier_sample,hz]
  obtain ⟨hside,hrad⟩ := hs hnon
  constructor
  · change 0 ≤ ⟪ω,x⟫_ℝ
    change 0 ≤ ⟪ω,R⁻¹ • x⟫_ℝ at hside
    rwa [real_inner_smul_right,mul_nonneg_iff_of_pos_left (inv_pos.mpr hR)] at hside
  · simpa [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos hR, inv_mul_eq_div,div_le_iff₀ hR] using hrad

/-- Each atom surviving the physical half-ball cutoff contributes one
rank-one matrix. The bound counts sites once and allows arbitrary complex
weights and arbitrary evaluation points (including repeated points). -/
theorem sample_rank_le_half_ball {μ : TemperedDistribution (V p) ℂ} {A : Set (V p)}
    (hA : LocallyFiniteSites A) (hμ : LocalAtoms μ A) {h : SchwartzMap (V p) ℂ} {ω : V p}
    (hs : Function.support (𝓕 h : SchwartzMap (V p) ℂ) ⊆ halfBall ω 1)
    {R : ℝ} (hR : 0 < R) (s : V p) {ι : Type*} [Fintype ι] (x : ι → V p) :
    Matrix.rank (fun i j : ι => (𝓕 μ) (sample h R hR (s+x i-x j))) ≤ (A ∩ halfBall ω R).ncard := by
  classical
  obtain ⟨a,_,hμ⟩ := hμ
  let S := sites hA ω R
  let P : Finset A := S.preimage Subtype.val Subtype.val_injective.injOn
  have hP (u : A) : u ∈ P ↔ u.val ∈ halfBall ω R := by simp [P,S,u.property]
  have hcard : P.card = (A ∩ halfBall ω R).ncard := by
    have himage : P.image Subtype.val = S := by
      ext z
      constructor
      · rintro hz
        obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
        exact (mem_sites ..).mpr ⟨u.property,(hP u).mp hu⟩
      · intro hz
        have hh := (mem_sites ..).mp hz
        exact Finset.mem_image.mpr ⟨⟨z,hh.1⟩,(hP _).mpr hh.2,rfl⟩
    have hsc : S.card = (A ∩ halfBall ω R).ncard := (Set.ncard_eq_toFinset_card _ _).symm
    rw [← hsc,← himage,Finset.card_image_of_injective _ Subtype.val_injective]
  have he (q : V p) :
      (𝓕 μ) (sample h R hR q) = ∑ u ∈ P, a u * (𝓕 (sample h R hR q)) u := by
    let φ := 𝓕 (sample h R hR q)
    have hφ := support_fourier_sample hs hR q
    have hc : HasCompactSupport φ := HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall 0 R) (fun _ hz => (hφ hz).2)
    exact (hμ φ hc).unique (hasSum_sum_of_ne_finset_zero (fun u hu => by
      have hz : φ u = 0 := by by_contra hn; exact hu ((hP _).mpr (hφ hn))
      simp [hz]))
  let c (u : P) := a u.val * phase (-⟪s,u.val.val⟫_ℝ) * ((R^p:ℝ)⁻¹ : ℂ) * (𝓕 h) (R⁻¹ • u.val.val)
  let U : Matrix ι P ℂ := fun i u => c u * phase (-⟪x i,u.val.val⟫_ℝ)
  let W : Matrix P ι ℂ := fun u j => phase ⟪x j,u.val.val⟫_ℝ
  have hprod : (fun i j : ι => (𝓕 μ) (sample h R hR (s+x i-x j))) = U * W := by
    ext i j
    rw [he,← Finset.sum_attach,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro u _
    rw [fourier_sample]
    simp only [inner_add_left,sub_eq_add_neg,neg_add,inner_neg_left,neg_neg,
      Poisson.phase_add,U,W,c]
    ring
  rw [hprod,← hcard]
  exact (Matrix.rank_mul_le_left U W).trans (by simpa using Matrix.rank_le_card_width U)

end HalfBall.Fourier
