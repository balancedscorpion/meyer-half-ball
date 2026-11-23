module
public import HalfBall.Classification.LocalRecovery
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall.Classification
open Set Metric MeasureTheory FourierTransform
open scoped FourierTransform Convolution
open MeyerGeneralProblem.LevOlevskii

private theorem small_bumps {p} {d : ℝ} (hd : 0 < d) :
    ∃ β γ : SchwartzMap (V p) ℂ, Function.support β ⊆ closedBall 0 (d/2) ∧
      Function.support γ ⊆ closedBall 0 (d/4) ∧
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) γ β 0 = 1 := by
  let b : ContDiffBump (0 : V p) := ⟨d/4,d/2,by positivity,by linarith⟩
  let g : ContDiffBump (0 : V p) := ⟨d/8,d/4,by positivity,by linarith⟩
  let B : V p → ℂ := Complex.ofRealCLM ∘ b
  let G : V p → ℂ := Complex.ofRealCLM ∘ g.normed volume
  have hB : HasCompactSupport B := b.hasCompactSupport.comp_left rfl
  have hG : HasCompactSupport G := g.hasCompactSupport_normed.comp_left rfl
  let β := hB.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let γ := hG.toSchwartzMap (Complex.ofRealCLM.contDiff.comp g.contDiff_normed)
  have hs (x : V p) (h : γ x ≠ 0) : x ∈ closedBall 0 (d/4) := by
    have hg : x ∈ Function.support (g.normed volume) := fun hz => h (by change ((g.normed volume x:ℝ):ℂ) = 0; simp [hz])
    rw [g.support_normed_eq] at hg
    exact ball_subset_closedBall hg
  refine ⟨β,γ,fun x hx => ?_,fun x hx => hs x hx,?_⟩
  · have hg : x ∈ Function.support b := fun hz => hx (by change ((b x:ℝ):ℂ) = 0; simp [hz])
    rw [b.support_eq] at hg; exact ball_subset_closedBall hg
  · rw [SchwartzMap.convolution_apply]
    change (∫ x : V p, γ x * β (0-x)) = 1
    have he (x : V p) : γ x * β (0-x) = γ x := by
      by_cases hx : γ x = 0
      · simp [hx]
      · have hβ : β (0-x) = 1 := by
          change ((b (0-x):ℝ):ℂ) = 1
          rw [b.one_of_mem_closedBall (by simpa [b] using hs x hx)]; norm_num
        rw [hβ,mul_one]
    simp_rw [he]
    change (∫ x : V p, ((g.normed volume x:ℝ):ℂ)) = 1
    simpa only [← integral_complex_ofReal,Complex.ofReal_one] using congrArg ((↑) : ℝ → ℂ) (g.integral_normed (μ := volume))

/-- For each spectral site b, one test isolates b. For every capped
physical set, its Fourier samples on that set admit an exact replacement
by a test in the fixed window with uniformly bounded sup norm. -/
theorem isolating_window_recovery (p M : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (B : Set (V p)), LocallyFiniteSites B → ∀ b ∈ B,
      ∃ (P : SchwartzMap (V p) ℂ) (C : ℝ), HasCompactSupport P ∧ P b = 1 ∧
        (∀ y ∈ B, y ≠ b → P y = 0) ∧ 0 ≤ C ∧
        ∀ E : Set (V p), LocallyFiniteSites E → BallCap E M →
          ∃ χ : SchwartzMap (V p) ℂ, Function.support χ ⊆ closedBall 0 D ∧
            (∀ y, ‖χ y‖ ≤ C) ∧ ∀ x ∈ E, (𝓕 χ) x = (𝓕 P) x := by
  obtain ⟨R,hR,hrecover⟩ := recover_enveloped_character p M
  refine ⟨R+2,by linarith,fun B hB b _ => ?_⟩
  obtain ⟨d,hd,_,hsep⟩ := anchor_isolation hB b
  let δ := min d 1
  have hδ : 0 < δ := lt_min hd zero_lt_one
  obtain ⟨β,γ,hβ,hγ,hzero⟩ := small_bumps (p := p) hδ
  let L := ContinuousLinearMap.mul ℂ ℂ
  let K := SchwartzMap.convolution L γ β
  let P := SchwartzMap.compSubConstCLM ℂ b K
  obtain ⟨U,hU,hrec⟩ := hrecover (-b) β (hβ.trans (closedBall_subset_closedBall (by linarith [show δ ≤ 1 from min_le_right ..])))
  have hcγ : HasCompactSupport (γ : V p → ℂ) := HasCompactSupport.intro (isCompact_closedBall _ _) fun _ h => not_not.mp (mt (@hγ _) h)
  have hcβ : HasCompactSupport (β : V p → ℂ) := HasCompactSupport.intro (isCompact_closedBall _ _) fun _ h => not_not.mp (mt (@hβ _) h)
  have hcK : HasCompactSupport (K : V p → ℂ) := by
    rw [show (K : V p → ℂ) = (γ : V p → ℂ) ⋆[L] (β : V p → ℂ) from funext (SchwartzMap.convolution_apply L γ β)]
    exact hcγ.convolution L hcβ
  have hγn : 0 ≤ ∫ x, ‖γ x‖ := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨P,(∫ x, ‖γ x‖)*U,hcK.comp_homeomorph (Homeomorph.subRight b),by simpa [P,K] using hzero,?_,
    mul_nonneg hγn hU,fun E hf he => ?_⟩
  · intro y hy hne
    by_contra hn
    have hm : y-b ∈ Function.support ((γ : V p → ℂ) ⋆[L] (β : V p → ℂ)) := by
      change K (y-b) ≠ 0 at hn
      simpa only [K,SchwartzMap.convolution_apply,Function.mem_support] using hn
    obtain ⟨z,hz,w,hw,he⟩ := support_convolution_subset L hm
    have hh := norm_add_le z w
    change z+w = y-b at he
    rw [he] at hh
    have h₁ : ‖z‖ ≤ δ/4 := by simpa using hγ hz
    have h₂ : ‖w‖ ≤ δ/2 := by simpa using hβ hw
    linarith [hsep y hy hne, show δ ≤ d from min_le_left ..]
  · obtain ⟨g,hg,hs,hu,hx⟩ := hrec E hf he
    have hcg : HasCompactSupport g := HasCompactSupport.intro (isCompact_closedBall _ _) fun _ h => not_not.mp (mt (@hs _) h)
    let Lr := ContinuousLinearMap.mul ℝ ℂ
    let f := (γ : V p → ℂ) ⋆[Lr] g
    have hc : HasCompactSupport f := hcγ.convolution Lr hcg
    let χ := hc.toSchwartzMap (hcγ.contDiff_convolution_left Lr (γ.smooth _) hg.locallyIntegrable)
    refine ⟨χ,?_,fun y => ?_,fun x hxE => ?_⟩
    · intro y hy
      have hm : y ∈ Function.support ((γ : V p → ℂ) ⋆[Lr] g) := hy
      obtain ⟨z,hz,w,hw,rfl⟩ := support_convolution_subset Lr hm
      have hz' : ‖z‖ ≤ δ/4 := by simpa using hγ hz
      have hw' : ‖w‖ ≤ R+1 := by simpa using hs hw
      simpa [mem_closedBall] using (norm_add_le z w).trans (by linarith [show δ ≤ 1 from min_le_right ..] : ‖z‖+‖w‖ ≤ R+2)
    · change ‖∫ z, γ z * g (y-z)‖ ≤ _
      rw [← integral_mul_const]
      apply norm_integral_le_of_norm_le (γ.integrable.norm.mul_const U)
      exact ae_of_all _ (fun z => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hu _) (norm_nonneg _))
    · change 𝓕 ((γ : V p → ℂ) ⋆[L] g) x = _
      rw [Real.fourier_mul_convolution_eq γ.integrable (hg.integrable_of_hasCompactSupport hcg),hx x hxE]
      have hP := fourier_test_add K (-b) x
      simp only [neg_neg] at hP
      have hK (z : V p) : (𝓕 K) z = (𝓕 γ) z * (𝓕 β) z := by
        dsimp only [K]; rw [SchwartzMap.fourier_convolution]; rfl
      change (𝓕 (γ : V p → ℂ)) x * _ = (𝓕 ((SchwartzMap.compSubConstCLM ℂ b) K)) x
      rw [hP,hK]
      rw [← SchwartzMap.fourier_coe]; ring

end HalfBall.Classification
