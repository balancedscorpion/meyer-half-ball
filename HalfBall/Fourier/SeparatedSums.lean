/-
The two separated-sampling estimates adapt AtomicSeries.lean and
SeparatedInterpolation.lean from Jamie Martin’s lev-olevskii-lattice-cover
at f78b7d12876f95be3bce8b37ee57684d51b21d9c, under the MIT licence.
See LICENSES/lev-olevskii-lattice-cover-MIT.txt.
-/
module

public import HalfBall.Statement
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic

public section
namespace HalfBall.Fourier
open MeasureTheory Metric Filter
open scoped Topology
noncomputable section

/-- A common packing bound for the inverse polynomial over arbitrary finite
families of sites with the specified separation. Translating the family does
not change the bound. -/
theorem separated_inverse_weight_bound {d : ℕ} {η : ℝ} (hη : 0 < η)
    (s : ℕ) (hs : d < s) :
    ∃ C : ℝ, ∀ {ι : Type*} (u : ι → V d)
      (_ : ∀ i j, i ≠ j → η ≤ dist (u i) (u j)) (t : Finset ι),
      ∑ i ∈ t, ((1 + ‖u i‖) ^ s)⁻¹ ≤ C := by
  classical
  let r := η / 2
  have hr : 0 < r := half_pos hη
  let w (y : V d) := ((1 + ‖y‖) ^ s)⁻¹
  let f (y : V d) := (1 + r) ^ s * w y
  have hw : Integrable w := by
    have hdim : (Module.finrank ℝ (V d) : ℝ) < (s : ℝ) := by
      simpa using (show (d : ℝ) < s by exact_mod_cast hs)
    simpa [w, Real.rpow_neg (by positivity : ∀ x : V d, 0 ≤ 1 + ‖x‖)] using
      (integrable_one_add_norm (μ := volume) hdim)
  have hf : Integrable f := hw.const_mul _
  let ballVolume := volume.real (ball (0 : V d) r)
  have hV : 0 < ballVolume := ENNReal.toReal_pos (measure_ball_pos volume _ hr).ne' measure_ball_lt_top.ne
  refine ⟨(∫ y, f y) / ballVolume, ?_⟩
  intro ι u hsep t
  let B (i : ι) := ball (u i) r
  have hlocal (x : ι) (y) (hy : y ∈ B x) : w (u x) ≤ f y := by
    have hnorm := norm_le_norm_add_norm_sub (u x) y
    rw [norm_sub_rev] at hnorm
    have hdist : ‖y - (u x)‖ < r := by simpa [B, dist_eq_norm] using hy
    have hbase : 1 + ‖y‖ ≤ (1 + r) * (1 + ‖(u x)‖) := by
      nlinarith [mul_nonneg hr.le (norm_nonneg (u x))]
    have hpow := pow_le_pow_left₀ (by positivity) hbase s
    rw [mul_pow] at hpow
    change _⁻¹ ≤ _ * _⁻¹
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    rwa [inv_mul_eq_div, div_le_iff₀ (by positivity)]
  have hxbound (x : ι) : w (u x) * ballVolume ≤ ∫ y in B x, f y := by
    have hconst : IntegrableOn (fun _ : V d => w (u x)) (B x) :=
      integrableOn_const measure_ball_lt_top.ne
    have h := setIntegral_mono_on hconst hf.integrableOn measurableSet_ball (hlocal x)
    simpa [B, setIntegral_const, Measure.addHaar_real_ball_center, ballVolume, mul_comm] using h
  apply (le_div_iff₀ hV).mpr
  rw [Finset.sum_mul]
  refine (Finset.sum_le_sum fun x _ => hxbound x).trans ?_
  rw [← integral_biUnion_finset t (s := B) (fun _ _ => measurableSet_ball) _ (fun _ _ => hf.integrableOn)]
  · apply setIntegral_le_integral hf (ae_of_all _ fun y => ?_)
    dsimp [f, w]; positivity
  · intro x _ y _ hne
    refine Set.disjoint_left.mpr fun z hx hy => ?_
    have hxy := hsep x y hne
    have htri := dist_triangle (u x) z (u y)
    have h1 : dist (u x) z < η / 2 := (mem_ball'.mp hx)
    have h2 : dist z (u y) < η / 2 := hy
    linarith


/-- The same dilation controls every column of every sampling matrix with
the given separation, including matrices on infinite carriers. -/
theorem separated_schwartz_offDiagonal {d : ℕ} (φ : SchwartzMap (V d) ℂ)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ {ι : Type*} [DecidableEq ι] (u : ι → V d)
      (_ : ∀ i j, i ≠ j → η ≤ dist (u i) (u j)) (j : ι) (t : Finset ι),
      (∑ i ∈ t with i ≠ j, ‖φ (L • (u i - u j))‖) ≤ ε := by
  classical
  let s := d + 1
  obtain ⟨C, hC⟩ := separated_inverse_weight_bound (d := d) hη s (Nat.lt_succ_self _)
  let D : ℝ := 2 ^ (s+1) * (Finset.Iic (s+1, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ
  have hD : 0 ≤ D := mul_nonneg (by positivity) (apply_nonneg _ _)
  have hφ (x : V d) : (1 + ‖x‖) ^ (s+1) * ‖φ x‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (s+1, 0)) le_rfl le_rfl φ x
  let L := max 1 (D * C / ε / η)
  have hL : 1 ≤ L := le_max_left ..
  have hL0 : 0 ≤ L := by linarith
  have hscale : D * C ≤ ε * (1 + L * η) := by
    have hh := (div_le_iff₀ hη).mp (le_max_right 1 (D * C / ε / η))
    have hh' := (div_le_iff₀ hε).mp hh
    change D * C ≤ ε * (1 + L * η)
    change D * C ≤ L * η * ε at hh'
    linarith
  refine ⟨L, hL, ?_⟩
  intro ι inst u hsep j t
  let v (i : ι) := u i - u j
  have hoff (i : ι) (hne : i ≠ j) :
      ‖φ (L • v i)‖ ≤ (D / (1 + L * η)) * ((1 + ‖v i‖) ^ s)⁻¹ := by
    have hηi : η ≤ ‖v i‖ := by simpa [v, ← dist_eq_norm] using hsep i j hne
    have hn : ‖L • v i‖ = L * ‖v i‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hL0]
    have hi : 1 + ‖v i‖ ≤ 1 + ‖L • v i‖ := by rw [hn]; nlinarith [norm_nonneg (v i)]
    have hb : 1 + L * η ≤ 1 + ‖L • v i‖ := by rw [hn]; gcongr
    have hp : (1 + ‖v i‖)^s * (1 + L * η) ≤ (1 + ‖L • v i‖)^(s+1) := by
      exact (mul_le_mul (pow_le_pow_left₀ (by positivity) hi _) hb (by positivity) (by positivity)).trans_eq (pow_succ _ s).symm
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
    calc
      _ = ‖φ (L • v i)‖ * ((1 + ‖v i‖)^s * (1 + L * η)) := by ring
      _ ≤ ‖φ (L • v i)‖ * (1 + ‖L • v i‖)^(s+1) := by gcongr
      _ ≤ D := by simpa [mul_comm] using hφ (L • v i)
  have hsum := hC v (fun i k hik => by simpa [v] using hsep i k hik) (t.filter (· ≠ j))
  calc
    _ ≤ ∑ i ∈ t with i ≠ j, (D / (1 + L * η)) * ((1 + ‖v i‖)^s)⁻¹ :=
      Finset.sum_le_sum fun i hi => hoff i (Finset.mem_filter.mp hi).2
    _ ≤ D / (1 + L * η) * C := by rw [← Finset.mul_sum]; gcongr
    _ ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      exact hscale


/-- A uniform absolute row sum for a unit-separated cloud, independent
of the number of vertices, the centre and the translation of the cloud. -/
theorem separated_sample_sum {p : ℕ} (h : SchwartzMap (V p) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} (y : ι → V p),
      (∀ i j, i ≠ j → 1 ≤ dist (y i) (y j)) → ∀ F : Finset ι, ∑ i ∈ F, ‖h (y i)‖ ≤ C := by
  let k := p+1
  obtain ⟨C,hC⟩ := separated_inverse_weight_bound (d := p) zero_lt_one k (Nat.lt_succ_self _)
  let K := 2^k * (Finset.Iic (k,0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h
  have hK : 0 ≤ K := mul_nonneg (by positivity) (apply_nonneg _ _)
  refine ⟨K*max C 0,mul_nonneg hK (le_max_right ..),?_⟩
  intro ι y hy F
  calc ∑ i ∈ F, ‖h (y i)‖ ≤ ∑ i ∈ F, K*((1+‖y i‖)^k)⁻¹ := by
         apply Finset.sum_le_sum; intro i _
         rw [← div_eq_mul_inv,le_div_iff₀ (by positivity),mul_comm]
         simpa only [norm_iteratedFDeriv_zero] using
           SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k,0)) le_rfl le_rfl h (y i)
       _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left ((hC y hy F).trans (le_max_left ..)) hK

end
end HalfBall.Fourier
