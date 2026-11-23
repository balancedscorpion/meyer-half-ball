module
public import HalfBall.Classification.Bandwidth
public import HalfBall.Fourier.PhysicalRank
public import HalfBall.Fourier.SeparatedSums
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall.Classification
open Set Metric FourierTransform Finset
open scoped FourierTransform
open MeyerGeneralProblem.LevOlevskii

private theorem solve_bounded {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℂ)
    (hd : ∀ i, K i i = 1) (hr : ∀ i, ∑ j ∈ univ.erase i, ‖K i j‖ ≤ 1/2)
    (b : ι → ℂ) (hb : ∀ i, ‖b i‖ ≤ 1) :
    ∃ c : ι → ℂ, (∀ i, ‖c i‖ ≤ 2) ∧ K.mulVec c = b := by
  have hdet := det_ne_zero_of_sum_row_lt_diag (A := K) (fun i => (hr i).trans_lt (by rw [hd]; norm_num))
  let c := K⁻¹.mulVec b
  have he : K.mulVec c = b := by
    dsimp [c]; rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),Matrix.one_mulVec]
  refine ⟨c,fun j => ?_,he⟩
  obtain ⟨i,_,hmax⟩ := univ.exists_max_image (fun k => ‖c k‖) ⟨j,mem_univ _⟩
  have hh : c i = b i - ∑ k ∈ univ.erase i,K i k*c k := by
    have hh := congrFun he i
    change ∑ k, K i k*c k = b i at hh
    rw [← sum_erase_add _ _ (mem_univ i),hd,one_mul] at hh
    rw [← hh]; ring
  have hnorm := norm_sub_le (b i) (∑ k ∈ univ.erase i, K i k*c k)
  rw [← hh] at hnorm
  have hrest : ‖∑ k ∈ univ.erase i, K i k*c k‖ ≤ (1/2)*‖c i‖ := by
    calc _ ≤ ∑ k ∈ univ.erase i, ‖K i k * c k‖ := norm_sum_le ..
         _ ≤ ∑ k ∈ univ.erase i, ‖K i k‖ * ‖c i‖ := sum_le_sum (fun k _ => by
           rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hmax k (mem_univ _)) (norm_nonneg _))
         _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (hr _) (norm_nonneg _)
  exact (hmax j (mem_univ _)).trans (by linarith [hb i])

/-- A fixed band and a fixed sup norm bound suffice to interpolate arbitrary
unit-bounded data on any finite separated class. -/
theorem finite_separated_interpolation (p : ℕ) :
    ∃ r C : ℝ, 0 ≤ r ∧ 1 ≤ C ∧ ∀ (E : Finset (V p)),
      (E : Set (V p)).Pairwise (fun x y => 1 ≤ dist x y) → ∀ b : E → ℂ, (∀ i, ‖b i‖ ≤ 1) →
      ∃ f : V p → ℂ, Bandwidth r f ∧ (∀ x, ‖f x‖ ≤ C) ∧ ∀ i : E, f i = b i := by
  classical
  obtain ⟨a,ha,his⟩ := bandlimited_isolation_at_point p (η := 1) zero_lt_one
  obtain ⟨φ,hφ,h0,_⟩ := his ∅ (by simp) 0
  let k := 𝓕 φ
  obtain ⟨L,hL,hrows⟩ := Fourier.separated_schwartz_offDiagonal k (η := 1) (ε := 1/2) zero_lt_one (by norm_num)
  have hLpos : 0 < L := by linarith
  let κ := Fourier.sample k L hLpos 0
  obtain ⟨A,hA,hpack⟩ := Fourier.separated_sample_sum κ
  refine ⟨L*a,max 1 (2*A),mul_nonneg hLpos.le ha.le,le_max_left ..,fun E hE b hb => ?_⟩
  let K : Matrix E E ℂ := fun i j => k (L • (i.val-j.val))
  have hd (i : E) : K i i = 1 := by simpa [K,k] using h0
  have hr (i : E) : ∑ j ∈ univ.erase i, ‖K i j‖ ≤ 1/2 := by
    have hs (j l : E) (hjl : j ≠ l) : 1 ≤ dist (-j.val) (-l.val) := by
      simpa using hE j.property l.property (fun h => hjl (Subtype.ext h))
    have h := hrows (fun j : E => -j.val) hs i univ
    have heq : univ.filter (fun j : E => j ≠ i) = univ.erase i := by ext; simp
    rw [heq] at h
    simpa only [K,neg_sub_neg] using h
  obtain ⟨c,hn,hc⟩ := solve_bounded K hd hr b hb
  let g (i : E) := Fourier.sample k L hLpos i.val
  have hg (i : E) : Bandwidth (L*a) (g i : V p → ℂ) := by
    let θ := 𝓕⁻ (g i)
    have hs : Function.support θ ⊆ closedBall 0 (L*a) := by
      intro x hx
      change (𝓕 (g i)) (-x) ≠ 0 at hx
      rw [Fourier.fourier_sample] at hx
      have hn := (mul_ne_zero_iff.mp hx).2
      change (𝓕 (𝓕 φ)) (L⁻¹ • -x) ≠ 0 at hn
      have he := congrArg (fun ψ : SchwartzMap (V p) ℂ => ψ (-(L⁻¹ • -x))) (fourierInv_fourier_eq (F := SchwartzMap (V p) ℂ) φ)
      change (𝓕 (𝓕 φ)) (- -(L⁻¹ • -x)) = φ (-(L⁻¹ • -x)) at he
      rw [neg_neg] at he
      rw [he] at hn
      have hh := hφ hn
      simpa [mem_closedBall,norm_smul,Real.norm_eq_abs,abs_of_pos hLpos,inv_mul_eq_div,div_le_iff₀ hLpos,mul_comm] using hh
    simpa only [θ,fourier_fourierInv_eq] using Bandwidth.of_fourier θ hs
  refine ⟨fun x => ∑ i : E,c i * g i x,Bandwidth.sum univ _ (by positivity) (fun i _ => (hg i).smul _),fun x => ?_,fun i => ?_⟩
  · have hs (i j : E) (hne : i ≠ j) : 1 ≤ dist (x-i.val) (x-j.val) := by
      rw [show x-i.val = x + (-i.val) by abel,show x-j.val = x + (-j.val) by abel,dist_add_left,dist_neg_neg]
      exact hE i.property j.property (fun h => hne (Subtype.ext h))
    have hpack' := hpack (fun i : E => x-i.val) hs univ
    calc _ ≤ ∑ i : E, ‖c i*g i x‖ := norm_sum_le ..
         _ ≤ ∑ i : E, 2*‖κ (x-i.val)‖ := sum_le_sum (fun i _ => by
           simp only [norm_mul,κ,g,Fourier.sample_apply,sub_zero]
           exact mul_le_mul_of_nonneg_right (hn _) (norm_nonneg _))
         _ ≤ max 1 (2*A) := by rw [← Finset.mul_sum]; exact (by gcongr : 2* _ ≤ 2*A) |>.trans (le_max_right ..)
  · simpa [K,g,Matrix.mulVec,dotProduct,mul_comm] using congrFun hc i

end HalfBall.Classification
