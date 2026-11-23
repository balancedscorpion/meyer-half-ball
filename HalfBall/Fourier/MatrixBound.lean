module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

@[expose] public section
namespace HalfBall.Fourier

open Finset
/-- A weighted strict row bound on the perturbation of a scalar matrix
implies full rank. The row weights allow upper blocks of arbitrary fixed
size, while small errors in the lower blocks are absorbed at a late scale. -/
theorem rank_of_weighted_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (a : ℂ) (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    (h : ∀ i, ∑ j, ‖K i j - (if j = i then a else 0)‖ * t j < ‖a‖*t i) :
    K.rank = Fintype.card ι := by
  classical
  have hker (v : ι → ℂ) (hv : K.mulVec v = 0) : v = 0 := by
    by_contra hne
    obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra! h; exact hne (funext h)
    let : Nonempty ι := ⟨j⟩
    let f i := ‖v i‖ / t i
    obtain ⟨i,_,hmax⟩ := univ.exists_max_image f univ_nonempty
    have hpos : 0 < f i := (div_pos (norm_pos_iff.mpr hj) (ht j)).trans_le (hmax j (mem_univ _))
    have hbound (k) : ‖v k‖ ≤ f i * t k := (div_le_iff₀ (ht k)).mp (hmax k (mem_univ _))
    have he : ∑ k, (K i k - (if k = i then a else 0))*v k = -(a*v i) := by
      simp_rw [sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul]
      have hk : ∑ k, K i k*v k = 0 := congrFun hv i
      simp [hk]
    have hh := norm_sum_le (s := univ) (f := fun k => (K i k-(if k=i then a else 0))*v k)
    rw [he,norm_neg,norm_mul] at hh
    simp only [norm_mul] at hh
    have hcontra := calc
      ‖a‖*‖v i‖ ≤ ∑ k, ‖K i k-(if k=i then a else 0)‖*‖v k‖ := hh
      _ ≤ ∑ k, ‖K i k-(if k=i then a else 0)‖*(f i*t k) := by
        apply sum_le_sum; intro k _; exact mul_le_mul_of_nonneg_left (hbound k) (norm_nonneg _)
      _ = f i * ∑ k, ‖K i k-(if k=i then a else 0)‖*t k := by
        rw [Finset.mul_sum]; apply sum_congr rfl; intro k _; ring
      _ < f i * (‖a‖*t i) := mul_lt_mul_of_pos_left (h i) hpos
      _ = ‖a‖*‖v i‖ := by dsimp [f]; field_simp [(ht i).ne']
    exact (lt_irrefl _) hcontra
  have hinj : Function.Injective K.mulVecLin := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hker)
  rw [Matrix.rank,LinearMap.finrank_range_of_inj hinj,Module.finrank_pi]

end HalfBall.Fourier
