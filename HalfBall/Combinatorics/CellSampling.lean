module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Finset
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def weight (q : ℝ) (b : Bool) := if b then q else 1-q

def mass (q : ℝ) (ω : κ → Bool) := ∏ i, weight q (ω i)

/-- Coarse cells are independently occupied with probability q. -/
noncomputable def cellMean (q : ℝ) (f : (κ → Bool) → ℝ) := ∑ ω, mass q ω * f ω

theorem cellMean_event (q : ℝ) (D : Finset κ) :
    cellMean q (fun ω => if ∀ i ∈ D, ω i = true then 1 else 0) = q^D.card := by
  classical
  let term (i : κ) (b : Bool) := if i ∈ D ∧ b=false then 0 else weight q b
  have h (ω : κ → Bool) : mass q ω * (if ∀ i ∈ D, ω i=true then 1 else 0) = ∏ i, term i (ω i) := by
    by_cases hs : ∀ i ∈ D, ω i=true
    · rw [ite_eq_left hs,mul_one]
      exact prod_congr rfl fun i _ => by
        dsimp [term]
        split_ifs with hh
        · simp [hs i hh.1] at hh
        · rfl
    · rw [ite_eq_right hs,mul_zero]
      push Not at hs
      obtain ⟨i,hi,hω⟩ := hs
      exact (prod_eq_zero (mem_univ i) (by simp [term,hi,Bool.eq_false_iff.mpr hω])).symm
  have hcoord (i : κ) : ∑ b, term i b = if i ∈ D then q else 1 := by
    rw [Fintype.sum_bool]; by_cases hi : i ∈ D <;> simp [term,weight,hi]
  simp only [cellMean,h,← Fintype.prod_sum,hcoord,prod_ite_mem,univ_inter,prod_const]

/-- Count configurations whose distinct coarse cells have all been occupied. -/
theorem cellMean_count {ι : Type*} (q : ℝ) (events : Finset ι) (cells : ι → Finset κ) :
    cellMean q (fun ω => (events.filter fun x => ∀ i ∈ cells x, ω i=true).card) =
      ∑ x ∈ events, q^(cells x).card := by
  classical
  have hc (ω : κ → Bool) : ((events.filter fun x => ∀ i ∈ cells x, ω i=true).card : ℝ) =
      ∑ x ∈ events, if ∀ i ∈ cells x, ω i=true then (1 : ℝ) else 0 := (sum_boole ..).symm
  simp_rw [cellMean,hc,mul_sum]
  rw [sum_comm]
  exact sum_congr rfl (fun x _ => cellMean_event q (cells x))

theorem cellMean_const (q c : ℝ) : cellMean (κ := κ) q (fun _ => c) = c := by
  have h : ∑ ω : κ → Bool, mass q ω = 1 := by simpa [cellMean] using cellMean_event q (∅ : Finset κ)
  simp [cellMean,← sum_mul,h]

theorem cellMean_sub (q : ℝ) (f g : (κ → Bool) → ℝ) :
    cellMean q (fun w => f w - g w) = cellMean q f - cellMean q g := by simp [cellMean,mul_sub,sum_sub_distrib]

theorem cellMean_mul (q c : ℝ) (f : (κ → Bool) → ℝ) :
    cellMean q (fun w => c * f w) = c * cellMean q f := by
  unfold cellMean
  rw [mul_sum]
  exact sum_congr rfl (fun _ _ => by ring)

theorem exists_ge_cellMean {q : ℝ} (hq : q ∈ Set.Icc 0 1) (f : (κ → Bool) → ℝ) :
    ∃ w, cellMean q f ≤ f w := by
  classical
  obtain ⟨w,_,hw⟩ := univ.exists_max_image f univ_nonempty
  refine ⟨w,?_⟩
  calc _ ≤ cellMean q (fun _ => f w) := by
         apply sum_le_sum
         intro x _
         apply mul_le_mul_of_nonneg_left (hw x (mem_univ _))
         apply prod_nonneg
         intro i _
         dsimp [weight]; split <;> linarith [hq.1,hq.2]
       _ = _ := cellMean_const q _

end HalfBall
