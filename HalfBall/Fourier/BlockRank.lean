module

public import HalfBall.Fourier.MatrixBound
import Mathlib.Tactic

@[expose] public section
namespace HalfBall.Fourier
open Finset

/-- An ordered block matrix retains full rank under a uniform entrywise
error whose product with the total number of columns is small. The threshold
depends on the number of blocks and their upper row bound, independently of
the sample sizes inside them. -/
theorem rank_of_ordered_blocks (m : ℕ) (a : ℂ) (ha : a ≠ 0) (H : ℝ) (hH : 0 ≤ H) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Y : Fin m → Type) [∀ j, Fintype (Y j)] [∀ j, DecidableEq (Y j)]
      (K M : Matrix (Sigma Y) (Sigma Y) ℂ) (e : ℝ), 0 ≤ e → (Fintype.card (Sigma Y):ℝ)*e ≤ δ →
      (∀ i j, ‖K i j-M i j‖ ≤ e) →
      (∀ (i : Sigma Y) (j : Fin m),
        (∑ y : Y j, ‖M i ⟨j,y⟩ - (if (⟨j,y⟩ : Sigma Y) = i then a else 0)‖) ≤
        if j = i.1 then ‖a‖/4 else if i.1 < j then H else 0) →
      K.rank = Fintype.card (Sigma Y) := by
  classical
  have ha' := norm_pos_iff.mpr ha
  let ratio := min (1:ℝ) (‖a‖/(4*((m:ℝ)+1)*(H+1)))
  have hratio : 0 < ratio := lt_min zero_lt_one (div_pos ha' (by positivity))
  have h1 : ratio ≤ 1 := min_le_left ..
  have hscale : m*ratio*H ≤ ‖a‖/4 := by
    have hq : ratio * (4*((m:ℝ)+1)*(H+1)) ≤ ‖a‖ := (le_div_iff₀ (by positivity : 0 < 4*((m:ℝ)+1)*(H+1))).mp (min_le_right 1 _)
    change ratio * _ ≤ _ at hq
    nlinarith [mul_nonneg (Nat.cast_nonneg m) hratio.le, mul_nonneg hratio.le hH]
  let t (i : Fin m) := ratio^i.val
  have ht (i : Fin m) : 0 < t i := pow_pos hratio _
  have ht1 (i : Fin m) : t i ≤ 1 := pow_le_one₀ hratio.le h1
  have htmin (i : Fin m) : ratio^m ≤ t i := pow_le_pow_of_le_one hratio.le h1 i.isLt.le
  have htlt {i j : Fin m} (hij : i < j) : t j ≤ t i * ratio := by
    rw [show t i * ratio = ratio^(i.val+1) from (pow_succ ..).symm]
    exact pow_le_pow_of_le_one hratio.le h1 (Nat.succ_le_of_lt hij)
  refine ⟨‖a‖/4 * ratio^m,by positivity,?_⟩
  intro Y _ _ K M e he hδ herr hrows
  apply rank_of_weighted_rows K a (fun i => t i.1) (fun i => ht _)
  intro i
  let c (j : Sigma Y) := if j=i then a else 0
  have hmodel (j : Fin m) :
      (∑ y : Y j, ‖M i ⟨j,y⟩-c ⟨j,y⟩‖ * t j) ≤
      (if j=i.1 then ‖a‖/4 * t i.1 else 0) + H*(t i.1*ratio) := by
    rw [← Finset.sum_mul]
    have h := mul_le_mul_of_nonneg_right (hrows i j) (ht j).le
    change _ ≤ _ at h
    by_cases heq : j=i.1
    · simp only [heq,ite_true] at h ⊢
      exact h.trans (le_add_of_nonneg_right (by positivity))
    · simp only [heq,ite_false,zero_add] at h ⊢
      by_cases hij : i.1 < j
      · simp only [hij,ite_true] at h; exact h.trans (mul_le_mul_of_nonneg_left (htlt hij) hH)
      · simp only [hij,ite_false,zero_mul] at h; exact h.trans (by positivity)
  have hsumModel : (∑ j : Sigma Y, ‖M i j-c j‖ * t j.1) ≤ ‖a‖/4*t i.1 + (m*ratio*H)*t i.1 := by
    rw [Fintype.sum_sigma]
    refine (sum_le_sum (fun j _ => hmodel j)).trans_eq ?_
    simp [Finset.sum_add_distrib]
    ring
  have hsumErr : (∑ j : Sigma Y, ‖K i j-M i j‖*t j.1) ≤ ‖a‖/4*t i.1 := by
    calc _ ≤ ∑ _j : Sigma Y, e := sum_le_sum (fun j _ => (mul_le_mul (herr i j) (ht1 _) (ht _).le he).trans_eq (mul_one _))
         _ = (Fintype.card (Sigma Y):ℝ)*e := by simp
         _ ≤ _ := hδ.trans (mul_le_mul_of_nonneg_left (htmin _) (by positivity))
  have hboth := calc
    (∑ j : Sigma Y, ‖K i j-c j‖*t j.1) ≤ ∑ j : Sigma Y, (‖K i j-M i j‖+‖M i j-c j‖)*t j.1 := by
      apply sum_le_sum; intro j _; exact mul_le_mul_of_nonneg_right (norm_sub_le_norm_sub_add_norm_sub ..) (ht _).le
    _ = (∑ j : Sigma Y, ‖K i j-M i j‖*t j.1) + ∑ j : Sigma Y, ‖M i j-c j‖*t j.1 := by
      simp [add_mul,Finset.sum_add_distrib]
    _ ≤ _ := add_le_add hsumErr hsumModel
  exact hboth.trans_lt (by nlinarith [mul_le_mul_of_nonneg_right hscale (ht i.1).le,mul_pos ha' (ht i.1)])

end HalfBall.Fourier
