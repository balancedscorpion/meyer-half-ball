module
public import HalfBall.Classification.BoundedInterpolation
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall.Classification
open Finset Metric Set
open MeyerGeneralProblem.LevOlevskii

/-- Telescoping powers at the earlier colour classes. No denominator
involving the separation of two different classes occurs. -/
private theorem telescope (z : ℂ) (h : ℕ → ℂ) (h0 : h 0 = 1) (n : ℕ) :
    h n + ∑ j ∈ range n, z^(n-1-j) * (z*h j-h (j+1)) = z^n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [sum_range_succ]
    have hs : ∑ j ∈ range n, z^(n+1-1-j)*(z*h j-h (j+1)) =
        z * ∑ j ∈ range n, z^(n-1-j)*(z*h j-h (j+1)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hlt := mem_range.mp hj
      rw [show n+1-1-j = (n-1-j)+1 by omega,pow_succ]
      ring
    rw [hs,show n+1-1-n = 0 by omega,pow_zero,one_mul,pow_succ]
    linear_combination z * ih

/-- A fixed bandwidth suffices to interpolate every power of a character
of frequency norm at most one. The sup norm bound may depend on the power.
On the newest colour class each residual X hⱼ − hⱼ₊₁ vanishes. On every
earlier class the sum telescopes. -/
theorem powers_on_separated_classes (p m : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ n : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : Fin m → Finset (V p)),
      (∀ i, (F i : Set (V p)).Pairwise (fun x y => 1 ≤ dist x y)) →
      ∀ (X : V p → ℂ), Bandwidth 1 X → (∀ x, ‖X x‖ = 1) →
      ∃ f : V p → ℂ, Bandwidth R f ∧ (∀ x, ‖f x‖ ≤ C) ∧ ∀ i x, x ∈ F i → f x = X x ^ n := by
  classical
  induction m with
  | zero =>
    exact ⟨0,le_rfl,fun _ => ⟨1,le_rfl,fun _ _ _ _ _ =>
      ⟨fun _ => 0,Bandwidth.const 0,fun _ => by norm_num,fun i => i.elim0⟩⟩⟩
  | succ m ih =>
    obtain ⟨r,hr,hprev⟩ := ih
    obtain ⟨s,A,hs,hA,hinterp⟩ := finite_separated_interpolation p
    choose D hD hsolve using hprev
    refine ⟨r+(1+s),by linarith,fun n => ?_⟩
    let C := A + ∑ j ∈ range n,D (n-1-j)*(A+A)
    have hC : 1 ≤ C := hA.trans (le_add_of_nonneg_right (sum_nonneg (fun j _ => by
      have := hD (n-1-j); positivity)))
    refine ⟨C,hC,fun F hF X hX hnorm => ?_⟩
    have hsingle (j : ℕ) := hinterp (F 0) (hF 0)
      (fun z => X z ^ (j+1)) (fun z => by simp [norm_pow,hnorm])
    choose h₁ hband hbound hval using hsingle
    let h : ℕ → V p → ℂ := Nat.rec (fun _ => 1) (fun j _ => h₁ j)
    have hh (j) : Bandwidth s (h j) := by cases j with
      | zero => exact (Bandwidth.const 1).mono hs
      | succ j => exact hband j
    have hq (j x) : ‖h j x‖ ≤ A := by cases j with
      | zero => simpa [h] using hA
      | succ j => exact hbound j x
    have hv (j x) (hx : x ∈ F 0) : h j x = X x ^ j := by cases j with
      | zero => simp [h]
      | succ j => exact hval j ⟨x,hx⟩
    choose g hgB hgN hgV using fun k => hsolve k (fun i => F i.succ) (fun i => hF i.succ) X hX hnorm
    let term (j : ℕ) (x : V p) := g (n-1-j) x * (X x * h j x - h (j+1) x)
    have hw (j) : Bandwidth (r+(1+s)) (term j) :=
      (hgB _).mul ((hX.mul (hh j)).sub ((hh (j+1)).mono (by linarith)))
    refine ⟨fun x => h n x + ∑ j ∈ range n,term j x,
      ((hh n).mono (by linarith)).add (Bandwidth.sum _ _ (by linarith) (fun j _ => hw j)),
      fun x => ?_,Fin.cases (fun x hx => ?_) (fun i x hx => ?_)⟩
    · apply (norm_add_le ..).trans
      apply add_le_add (hq _ _) ((norm_sum_le ..).trans ?_)
      apply sum_le_sum
      intro j _
      dsimp only [term]
      rw [norm_mul]
      apply mul_le_mul (hgN _ _) _ (norm_nonneg _) (by linarith [hD (n-1-j)])
      apply (norm_sub_le ..).trans
      simpa [norm_mul,hnorm] using add_le_add (hq j x) (hq (j+1) x)
    · have hz j : term j x = 0 := by simp [term,hv _ x hx,pow_succ',mul_comm]
      simp [hz,hv _ x hx]
    · have he j : g (n-1-j) x = X x ^ (n-1-j) := hgV _ i x hx
      simpa only [term,he] using telescope (X x) (fun j => h j x) rfl n

end HalfBall.Classification
