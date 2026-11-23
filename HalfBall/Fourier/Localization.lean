module

public import HalfBall.Fourier.Decay
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Fourier

open Filter Set MeasureTheory
open scoped Topology ContDiff NNReal

variable {p : ℕ}

def cut (b : ContDiffBump (0 : V p)) (ψ : SchwartzMap (V p) ℂ) : SchwartzMap (V p) ℂ :=
  (b.hasCompactSupport.smul_right (f' := (ψ : V p → ℂ))).toSchwartzMap (b.contDiff.smul (ψ.smooth _))

private theorem cutoff_deriv (b : ContDiffBump (0 : V p)) (i : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖iteratedFDeriv ℝ i b x‖ ≤ K := by
  let χ := b.hasCompactSupport.toSchwartzMap b.contDiff
  exact ⟨SchwartzMap.seminorm ℝ 0 i χ,apply_nonneg _ _,fun x => by
    change ‖iteratedFDeriv ℝ i χ x‖ ≤ _
    simpa using SchwartzMap.le_seminorm ℝ 0 i χ x⟩

/-- Removing a fixed compact cutoff which is one near all evaluation
centres leaves a rapidly decreasing error in every Schwartz seminorm. -/
theorem remainder_seminorm (h : SchwartzMap (V p) ℂ) {Q : ℝ} (hQ : 0 ≤ Q)
    (b : ContDiffBump (0 : V p)) (hb : Q+1 ≤ b.rIn) (k l N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ} (hR : 1 ≤ R) (q : V p), ‖q‖ ≤ Q →
      let ψ := sample h R (by linarith) q
      R^N * SchwartzMap.seminorm ℂ k l (ψ-cut b ψ) ≤ C := by
  classical
  choose D hD hbound using fun j => weighted_deriv_sample_le h hQ k j N
  choose K hK hχ using cutoff_deriv b
  let W (i : ℕ) := (l.choose i:ℝ)*K i
  have hW (i) : 0 ≤ W i := mul_nonneg (by positivity) (hK i)
  let C := D l + ∑ i ∈ Finset.range (l+1), W i * D (l-i)
  have hC : 0 ≤ C := add_nonneg (hD _) (Finset.sum_nonneg fun i _ => mul_nonneg (hW i) (hD _))
  refine ⟨C,hC,?_⟩
  intro R hR q hq ψ
  have hRpos : 0 < R^N := pow_pos (by linarith) _
  rw [mul_comm, ← le_div_iff₀ hRpos]
  apply SchwartzMap.seminorm_le_bound ℂ k l _ (div_nonneg hC hRpos.le)
  intro x
  by_cases hx : ‖x‖ < b.rIn
  · have he : (⇑(ψ-cut b ψ)) =ᶠ[𝓝 x] (0 : V p → ℂ) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      change ψ y - b y • ψ y = 0
      rw [b.one_of_mem_closedBall (by simpa using hy.le),one_smul,sub_self]
    rw [(he.iteratedFDeriv (𝕜 := ℝ) l).self_of_nhds]
    simp [div_nonneg hC hRpos.le]
  · have hdist : 1 ≤ ‖x-q‖ := by linarith [norm_le_norm_add_norm_sub q x,norm_sub_rev q x]
    let ξ := R^N * ‖x‖^k
    have hξ : 0 ≤ ξ := by dsimp [ξ]; positivity
    have hψ (j) : ξ * ‖iteratedFDeriv ℝ j ψ x‖ ≤ D j := hbound j hR q x hq hdist
    have hprod := norm_iteratedFDeriv_smul_le (b.contDiff : ContDiff ℝ ∞ b) (ψ.smooth _) x (n := l) (by simp)
    have hcut : ξ * ‖iteratedFDeriv ℝ l (cut b ψ) x‖ ≤ ∑ i ∈ Finset.range (l+1), W i * D (l-i) := by
      refine (mul_le_mul_of_nonneg_left hprod hξ).trans ?_
      rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _
      calc
        _ = ((l.choose i:ℝ)*‖iteratedFDeriv ℝ i b x‖) * (ξ*‖iteratedFDeriv ℝ (l-i) ψ x‖) := by ring
        _ ≤ W i * D (l-i) := mul_le_mul
          (mul_le_mul_of_nonneg_left (hχ i x) (by positivity)) (hψ _) (by positivity) (hW _)
    apply (le_div_iff₀ hRpos).mpr
    change ‖x‖^k * ‖iteratedFDeriv ℝ l ((ψ : V p → ℂ) - ⇑(cut b ψ)) x‖ * R^N ≤ _
    rw [iteratedFDeriv_sub_apply (ψ.smooth l).contDiffAt ((cut b ψ).smooth l).contDiffAt]
    calc
      _ = ξ * ‖iteratedFDeriv ℝ l ψ x - iteratedFDeriv ℝ l (cut b ψ) x‖ := by dsimp [ξ]; ring
      _ ≤ ξ * (‖iteratedFDeriv ℝ l ψ x‖ + ‖iteratedFDeriv ℝ l (cut b ψ) x‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le ..) hξ
      _ ≤ C := by rw [mul_add]; exact add_le_add (hψ l) hcut

/-- Uniform off-cutoff decay for an arbitrary tempered distribution. The
bound uses continuity on Schwartz space and makes no growth assumption on
the total variation of the atomic record. -/
theorem remainder_action (T : TemperedDistribution (V p) ℂ) (h : SchwartzMap (V p) ℂ)
    {Q : ℝ} (hQ : 0 ≤ Q) (b : ContDiffBump (0 : V p)) (hb : Q+1 ≤ b.rIn) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ} (hR : 1 ≤ R) (q : V p), ‖q‖ ≤ Q →
      let ψ := sample h R (by linarith) q
      R^N * ‖T ψ - T (cut b ψ)‖ ≤ C := by
  classical
  let v := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hv : Continuous v := continuous_norm.comp T.continuous
  obtain ⟨F,M,_,hM⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (V p) ℂ) v hv
  choose D hD hd using fun i : ℕ × ℕ => remainder_seminorm h hQ b hb i.1 i.2 N
  let K := ∑ i ∈ F, D i
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => hD i)
  refine ⟨M*K,mul_nonneg M.coe_nonneg hK,?_⟩
  intro R hR q hq ψ
  let g := ψ-cut b ψ
  have hr : 0 < R^N := pow_pos (by linarith) _
  have hsup : F.sup (schwartzSeminormFamily ℂ (V p) ℂ) g ≤ K / R^N := by
    apply Seminorm.finset_sup_apply_le (div_nonneg hK hr.le)
    intro i hi
    apply (le_div_iff₀ hr).mpr
    rw [mul_comm]
    exact (hd i hR q hq).trans (Finset.single_le_sum (fun a _ => hD a) hi)
  rw [← map_sub]
  have hnorm : ‖T g‖ ≤ (M:ℝ) * (K/R^N) := (hM g).trans (mul_le_mul_of_nonneg_left hsup M.coe_nonneg)
  calc R^N * ‖T g‖ ≤ R^N * ((M:ℝ)*(K/R^N)) := mul_le_mul_of_nonneg_left hnorm hr.le
       _ = _ := by field_simp

end HalfBall.Fourier
