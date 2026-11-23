module
public import HalfBall.Classification.WindowLimits
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall.Classification
open Set Filter Metric FourierTransform MeasureTheory Finset
open scoped FourierTransform Topology InnerProductSpace Convolution
open MeyerGeneralProblem.LevOlevskii

private theorem split_character {p} (u : V p) :
    ∃ (n : ℕ) (v : V p), ‖v‖ ≤ 1 ∧ ∀ x, (frequencyPhase v x : ℂ)^n = (frequencyPhase u x : ℂ) := by
  obtain ⟨n,hn⟩ := exists_nat_gt ‖u‖
  have hnpos : (0:ℝ)<n := (norm_nonneg _).trans_lt hn
  let v := (n:ℝ)⁻¹ • u
  refine ⟨n,v,?_,fun x => ?_⟩
  · simpa [v,norm_smul,Real.norm_eq_abs,abs_of_pos hnpos,inv_mul_eq_div,div_le_one hnpos] using hn.le
  · change (Real.fourierChar ⟪x,v⟫_ℝ : ℂ)^n = (Real.fourierChar ⟪x,u⟫_ℝ : ℂ)
    rw [← Circle.coe_pow,← AddChar.map_nsmul_eq_pow]
    congr 2
    rw [nsmul_eq_mul,show ⟪x,v⟫_ℝ = (n:ℝ)⁻¹*⟪x,u⟫_ℝ from real_inner_smul_right ..,← mul_assoc,mul_inv_cancel₀ hnpos.ne',one_mul]

/-- Within a fixed frequency window, bounded finite-sample interpolants
can reproduce an arbitrary character multiplied by a prescribed compact
test's Fourier transform. The continuous spectral kernel has a sup norm
bound independent of the geometry of the carrier. -/
theorem recover_enveloped_character (p M : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (u : V p) (β : SchwartzMap (V p) ℂ),
      Function.support β ⊆ closedBall 0 1 → ∃ U : ℝ, 0 ≤ U ∧
      ∀ E : Set (V p), LocallyFiniteSites E → BallCap E M →
        ∃ g : V p → ℂ, Continuous g ∧ Function.support g ⊆ closedBall 0 (R+1) ∧
          (∀ y, ‖g y‖ ≤ U) ∧ ∀ x ∈ E, 𝓕 g x = (frequencyPhase u x : ℂ) * (𝓕 β) x := by
  classical
  obtain ⟨R,hR,hinterp⟩ := powers_on_separated_classes p M
  refine ⟨R,hR,fun u β hβ => ?_⟩
  obtain ⟨n,v,hv,hpower⟩ := split_character u
  obtain ⟨C,hC,hpoly⟩ := hinterp n
  obtain ⟨U,hU,L,hUL⟩ := inverse_envelope_bounds (𝓕 β) (C := C) (by linarith)
  refine ⟨U,hU,fun E hf hcap => ?_⟩
  obtain ⟨F,hF,hsep⟩ := separated_classes_of_ballCap hcap
  let sites (j : ℕ) := (hf _ (isCompact_closedBall 0 (j:ℝ))).toFinset
  let G (j : ℕ) (i : Fin M) := (sites j).filter (fun x => x ∈ F i)
  have hG j i : (G j i : Set (V p)).Pairwise (fun x y => 1 ≤ dist x y) :=
    (hsep i).mono (fun _ hx => (mem_filter.mp hx).2)
  let X (x : V p) := (frequencyPhase v x : ℂ)
  choose f hbnd hnorm hs using fun j => hpoly (G j) (hG j) X ((Bandwidth.character v).mono hv) (fun _ => Circle.norm_coe _)
  choose ψ hψ hval using fun j => hbnd j 1 β hβ
  have hφ (j x) : ‖(𝓕 (ψ j)) x‖ ≤ C*‖(𝓕 β) x‖ := by
    rw [hval,norm_mul]; exact mul_le_mul_of_nonneg_right (hnorm j _) (norm_nonneg _)
  obtain ⟨g,hg,hgs,hgn,θ,hθ,ht⟩ := compact_window_subsequence ψ hψ
    (fun j => (hUL _ (hφ j)).1) (fun j => (hUL _ (hφ j)).2)
  refine ⟨g,hg,hgs,hgn,fun x hx => ?_⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hF ▸ hx)
  obtain ⟨j,hj⟩ := exists_nat_gt ‖x‖
  have he : ∀ᶠ k : ℕ in atTop, (𝓕 (ψ (θ k))) x = (frequencyPhase u x : ℂ)*(𝓕 β) x := by
    filter_upwards [hθ.tendsto_atTop.eventually_ge_atTop j] with k hk
    have hxj : x ∈ sites (θ k) := (Set.Finite.mem_toFinset _).mpr
      ⟨hx,by simpa using hj.le.trans (show (j:ℝ) ≤ θ k by exact_mod_cast hk)⟩
    rw [hval,hs (θ k) i x (mem_filter.mpr ⟨hxj,hi⟩),show X x^n = _ from hpower x]
  exact tendsto_nhds_unique (ht x) (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm))

end HalfBall.Classification
