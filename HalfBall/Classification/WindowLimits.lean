module
public import HalfBall.Classification.CharacterInterpolation
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall.Classification
open Set Filter Metric MeasureTheory FourierTransform
open scoped Topology FourierTransform InnerProductSpace NNReal BoundedContinuousFunction
open HalfBall.Poisson (phase)

/-- The oscillation of the inverse Fourier kernel is controlled by its
first physical moment. -/
private theorem phase_dist (a b : ℝ) : ‖phase a-phase b‖ ≤ 2*Real.pi*|a-b| := by
  have he : phase a-phase b = (phase (a-b)-1)*phase b := by
    rw [sub_mul,one_mul,← Poisson.phase_add,sub_add_cancel]
  rw [he,norm_mul,Poisson.norm_phase,mul_one]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(a-b))
  simpa [phase,Real.fourierChar_apply,mul_comm Complex.I,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos] using h

theorem inverse_envelope_bounds {p} (k : SchwartzMap (V p) ℂ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ U : ℝ, 0 ≤ U ∧ ∃ L : ℝ≥0, ∀ φ : SchwartzMap (V p) ℂ,
      (∀ x, ‖(𝓕 φ) x‖ ≤ C*‖k x‖) → (∀ x, ‖φ x‖ ≤ U) ∧ LipschitzWith L (φ : V p → ℂ) := by
  let K (x : V p) := C*‖k x‖
  let J (x : V p) := 2*Real.pi*C*(‖x‖*‖k x‖)
  have hK : Integrable K := k.integrable.norm.const_mul C
  have hJ : Integrable J := by simpa [J] using (k.integrable_pow_mul volume 1).const_mul (2*Real.pi*C)
  have hJ0 : 0 ≤ ∫ x,J x := integral_nonneg (fun x => by dsimp [J]; positivity)
  refine ⟨∫ x,K x,integral_nonneg (fun x => mul_nonneg hC (norm_nonneg _)),⟨_,hJ0⟩,fun φ hφ => ?_⟩
  let H (y x : V p) := phase ⟪x,y⟫_ℝ * (𝓕 φ) x
  have hint (y) : Integrable (H y) := by
    apply hK.mono' (by dsimp [H,phase]; fun_prop)
    exact ae_of_all _ (fun x => by simpa [H] using hφ x)
  have he (y) : φ y = ∫ x,H y x := by
    calc φ y = (𝓕⁻ (𝓕 φ)) y := by rw [fourierInv_fourier_eq]
         _ = _ := by rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq]; rfl
  refine ⟨fun x => ?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  · rw [he]
    exact (norm_integral_le_integral_norm _).trans (integral_mono (hint _).norm hK (fun z => by simpa [H] using hφ z))
  · rw [dist_eq_norm,he x,he y,← integral_sub (hint _) (hint _)]
    have hj := hJ.mul_const (dist x y)
    calc
      _ ≤ ∫ z, ‖H x z-H y z‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, J z * dist x y := integral_mono ((hint x).sub (hint y)).norm hj (fun z => by
        dsimp [H]; rw [← sub_mul,norm_mul]
        have hh := phase_dist ⟪z,x⟫_ℝ ⟪z,y⟫_ℝ
        rw [← inner_sub_right] at hh
        have hnorm := hh.trans (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z (x-y)) (by positivity))
        calc _ ≤ (2*Real.pi*(‖z‖*‖x-y‖)) * (C*‖k z‖) :=
                   mul_le_mul hnorm (hφ z) (norm_nonneg _) (by positivity)
             _ = _ := by dsimp [J]; rw [dist_eq_norm]; ring)
      _ = _ := integral_mul_const _ _

/-- A uniformly bounded Lipschitz family supported in one compact window
admits a continuous limit along a subsequence, including convergence of
its Fourier transforms at every point. -/
theorem compact_window_subsequence {p} (φ : ℕ → SchwartzMap (V p) ℂ) {R U : ℝ} {L : ℝ≥0}
    (hs : ∀ n, Function.support (φ n) ⊆ closedBall 0 R) (hu : ∀ n x, ‖φ n x‖ ≤ U)
    (hl : ∀ n, LipschitzWith L (φ n : V p → ℂ)) :
    ∃ g : V p → ℂ, Continuous g ∧ Function.support g ⊆ closedBall 0 R ∧ (∀ x, ‖g x‖ ≤ U) ∧
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ x, Tendsto (fun n => (𝓕 (φ (θ n))) x) atTop (𝓝 (𝓕 g x)) := by
  classical
  let K := closedBall (0 : V p) R
  have hK : IsCompact K := isCompact_closedBall _ _
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f (n : ℕ) : K →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact ⟨_,(φ n).continuous.comp continuous_subtype_val⟩
  have eqc : Equicontinuous ((↑) : range f → K → ℂ) := by
    intro x
    apply Metric.equicontinuousAt_iff.mpr
    intro ε hε
    refine ⟨ε/(L+1),by positivity,fun y hy i => ?_⟩
    obtain ⟨n,hn⟩ := i.property
    have hxy := (hl n).dist_le_mul y.val x.val
    have hlt := (lt_div_iff₀ (by positivity : 0 < (L:ℝ)+1)).mp hy
    rw [← hn,dist_comm]
    exact hxy.trans_lt (by change (L:ℝ)*dist y x < ε; nlinarith [show 0 ≤ dist y x from dist_nonneg])
  have hc := BoundedContinuousFunction.arzela_ascoli (closedBall (0:ℂ) U) (isCompact_closedBall ..)
    (range f) (fun g x hg => by obtain ⟨n,rfl⟩ := hg; simpa [f] using hu n x.val) eqc
  obtain ⟨G,_,θ,hθ,hlim⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  let g (x : V p) := if hx : x ∈ K then G ⟨x,hx⟩ else 0
  have hz (n x) (hx : x ∉ K) : φ n x = 0 := not_not.mp (mt (@hs n x) hx)
  have hg (x : V p) : Tendsto (fun n => φ (θ n) x) atTop (𝓝 (g x)) := by
    by_cases hx : x ∈ K
    · simpa [g,hx,f,Function.comp_def,BoundedContinuousFunction.mkOfCompact_apply] using ((continuous_eval_const (⟨x,hx⟩ : K)).tendsto G).comp hlim
    · simp [g,hx,hz _ _ hx]
  have hgLip : LipschitzWith L g := LipschitzWith.of_dist_le_mul fun x y =>
    le_of_tendsto ((hg x).dist (hg y)) (Eventually.of_forall fun n => (hl (θ n)).dist_le_mul x y)
  refine ⟨g,hgLip.continuous,fun x hx => by by_contra hout; exact hx (by simp [g,show x ∉ K from hout]),
    fun x => le_of_tendsto (hg x).norm (Eventually.of_forall fun n => hu (θ n) x),θ,hθ,fun y => ?_⟩
  let B := K.indicator (fun _ => U)
  have hB : Integrable B := (integrable_indicator_iff hK.isClosed.measurableSet).mpr
    (integrableOn_const hK.measure_lt_top.ne)
  simp only [SchwartzMap.fourier_coe,Real.fourier_eq]
  apply tendsto_integral_of_dominated_convergence B (fun n => by fun_prop) hB
  · intro n
    exact ae_of_all _ (fun x => by
      by_cases hx : x ∈ K
      · simpa [B,hx] using hu (θ n) x
      · simp [B,hx,hz _ _ hx])
  · exact ae_of_all _ (fun x => (hg x).const_smul _)

end HalfBall.Classification
