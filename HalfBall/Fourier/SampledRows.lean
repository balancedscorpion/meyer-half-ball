module

public import HalfBall.Fourier.OrderedModel
public import HalfBall.Fourier.SeparatedSums
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Fourier

open Finset Set
variable {p m : ℕ}

/-- Scale-independent width for the meshes of all patches. The ordering
affects only the unrestricted upper blocks of the sampled model. -/
theorem sampling_width (h : SchwartzMap (V p) ℂ) (h0 : h 0 = 1) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (m : ℕ) (s : V p) (U : Finset (V p)) (w : V p → ℂ),
    ∃ H : ℝ, 0 ≤ H ∧ ∀ {R : ℝ}, 0 < R → ∀ (Y : Fin m → Finset (V p)),
      (∀ j, (↑(Y j) : Set (V p)).Pairwise (fun x y => L/R ≤ dist x y)) →
      ∀ (i : Fin m) (x : Y i) (j : Fin m),
      (∑ y : Y j, ‖blockModel h s U w R i j (s+x.val-y.val) -
        (if (⟨j,y⟩ : Σ k, ↥(Y k)) = ⟨i,x⟩ then w s else 0)‖) ≤
        if j=i then ‖w s‖/4 else if i<j then H else 0 := by
  classical
  obtain ⟨L,hL,hoff⟩ := separated_schwartz_offDiagonal h zero_lt_one (by norm_num : (0:ℝ)<1/4)
  obtain ⟨A,hA,habs⟩ := separated_sample_sum h
  refine ⟨L,hL,fun m s U w => ⟨∑ u ∈ U, ‖w u‖*A,
    sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) hA),?_⟩⟩
  intro R hR Y hsep i x j
  have hLpos : 0 < L := by linarith
  have hd (j : Fin m) (y z : Y j) (hne : y ≠ z) : L ≤ R*dist y.val z.val := by
    have h' := hsep j y.property z.property (fun he => hne (Subtype.ext he))
    simpa [mul_comm] using (div_le_iff₀ hR).mp h'
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [hij.ne',ite_false,hij,ite_true]
    have hne (y : Y j) : (⟨j,y⟩ : Σ k, ↥(Y k)) ≠ ⟨i,x⟩ := fun he => hij.ne' (congrArg Sigma.fst he)
    simp only [hne,ite_false,sub_zero,blockModel,hij,ite_true]
    refine (sum_le_sum (fun y _ => norm_sum_le ..)).trans ?_
    rw [Finset.sum_comm]
    apply sum_le_sum
    intro u _
    simp_rw [norm_mul, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply habs (fun y : Y j => R • (u-(s+x.val-y.val))) _ univ
    intro y z hne'
    rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos hR,dist_eq_norm]
    have he : (u-(s+x.val-y.val))-(u-(s+x.val-z.val)) = y.val-z.val := by abel
    rw [he,← dist_eq_norm]
    exact hL.trans (hd _ y z hne')
  · simp only [ite_true,blockModel,lt_irrefl,ite_false]
    let v (y : Y i) := (R/L) • y.val
    have hv (y z : Y i) (hne : y ≠ z) : 1 ≤ dist (v y) (v z) := by
      rw [show dist (v y) (v z) = R/L*dist y.val z.val by simp [v,dist_smul₀,Real.norm_eq_abs,abs_of_pos hR,abs_of_pos hLpos]]
      rw [div_mul_eq_mul_div,le_div_iff₀ hLpos,one_mul]
      exact hd _ y z hne
    have hh := hoff v hv x univ
    have he (y : Y i) : L • (v y-v x) = R • (y.val-x.val) := by
      dsimp [v]; rw [← smul_sub,smul_smul]; congr 1; field_simp
    simp_rw [he] at hh
    have hpoint (y : Y i) : ‖w s * h (R • (s-(s+x.val-y.val))) -
        (if (⟨i,y⟩ : Σ k, ↥(Y k)) = ⟨i,x⟩ then w s else 0)‖ =
        if y ≠ x then ‖w s‖ * ‖h (R • (y.val-x.val))‖ else 0 := by
      rw [show s-(s+x.val-y.val) = y.val-x.val by abel]
      by_cases heq : y=x
      · simp [heq,h0]
      · simp [heq]
    simp_rw [hpoint]
    rw [← Finset.sum_filter,← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by ring)
  · have hne (y : Y j) : (⟨j,y⟩ : Σ k, ↥(Y k)) ≠ ⟨i,x⟩ := fun he => hji.ne (congrArg Sigma.fst he)
    simp [blockModel,not_lt_of_gt hji,hji.ne,hji.ne',hne]

end HalfBall.Fourier
