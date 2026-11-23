module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

@[expose] public section
namespace HalfBall.Poisson

open Filter MeasureTheory Set Topology
open scoped Topology

abbrev Coordinates (p : ℕ) := Fin p → ℝ
abbrev Indices (p : ℕ) := Fin p → ℤ
variable {p : ℕ}

def grid (n : Indices p) : Coordinates p := fun i => (n i : ℝ)

def project (x : Coordinates p) : UnitAddTorus (Fin p) := fun i => (x i : UnitAddCircle)

private theorem quotient_project : IsOpenQuotientMap (@project p) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

theorem project_add_grid (x : Coordinates p) (n : Indices p) : project (x+grid n) = project x := by
  funext i
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply AddSubgroup.mem_zmultiples_iff.mpr
  exact ⟨n i,by change (n i) • (1:ℝ) = x i + n i - x i; simp⟩

private theorem shift_of_project_eq {x y : Coordinates p} (h : project x = project y) :
    ∃ n : Indices p, x = y+grid n := by
  have hi (i : Fin p) := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp
    (congrFun h i : (x i : UnitAddCircle) = (y i : UnitAddCircle)))
  choose n hn using hi
  refine ⟨n,funext fun i => ?_⟩
  change x i = y i + n i
  have hh := hn i
  change n i • (1:ℝ) = x i - y i at hh
  simp only [zsmul_eq_mul, mul_one] at hh
  linarith

/-- Finitely many integer translates of a compact support meet a bounded ball.
The same index set works for every evaluation point in the ball. -/
theorem finite_shifts {f : Coordinates p → ℂ} (hf : HasCompactSupport f) (R : ℝ) :
    ∃ F : Finset (Indices p), ∀ x : Coordinates p, ‖x‖ ≤ R → ∀ n ∉ F, f (x+grid n) = 0 := by
  classical
  obtain ⟨D,hD⟩ := hf.isCompact.isBounded.subset_closedBall 0
  let b := ⌈R+D⌉₊
  let F := Fintype.piFinset (fun _ : Fin p => Finset.Icc (-(b:ℤ)) (b:ℤ))
  refine ⟨F,fun x hx n hn => ?_⟩
  by_contra hval
  have hnorm : ‖x+grid n‖ ≤ D := by
    simpa [Metric.mem_closedBall] using hD (subset_tsupport f hval)
  have hg : ‖grid n‖ ≤ R+D := by
    have hh := norm_sub_le (x+grid n) x
    rw [add_sub_cancel_left] at hh
    linarith
  apply hn; apply Fintype.mem_piFinset.mpr
  intro i
  have hab : |(n i : ℝ)| ≤ (b:ℝ) := (norm_le_pi_norm (grid n) i).trans (hg.trans (Nat.le_ceil _))
  exact Finset.mem_Icc.mpr (by exact_mod_cast (abs_le.mp hab))

noncomputable def periodSum (f : Coordinates p → ℂ) (x : Coordinates p) : ℂ := ∑' n : Indices p, f (x+grid n)

noncomputable section

private theorem periodSum_continuous {f : Coordinates p → ℂ} (hc : Continuous f)
    (hf : HasCompactSupport f) : Continuous (periodSum f) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro y
  obtain ⟨F,hF⟩ := finite_shifts hf (‖y‖+1)
  have hcont : Continuous (fun x : Coordinates p => ∑ n ∈ F, f (x+grid n)) := by fun_prop
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds y zero_lt_one] with x hx
  have hxbound := norm_le_norm_add_norm_sub y x
  have hd : ‖y-x‖ < 1 := by simpa [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hx
  have hnorm : ‖x‖ ≤ ‖y‖+1 := by linarith [norm_le_norm_add_norm_sub x y, norm_sub_rev x y]
  exact (hasSum_sum_of_ne_finset_zero (hF x hnorm)).tsum_eq

/-- Continuous periodization on the torus. Its defining evaluation formula
is supplied with the function so callers can work entirely in coordinates. -/
theorem exists_periodization {f : Coordinates p → ℂ} (hc : Continuous f)
    (hf : HasCompactSupport f) :
    ∃ P : C(UnitAddTorus (Fin p), ℂ), ∀ x, P (project x) = periodSum f x := by
  let q : C(Coordinates p,UnitAddTorus (Fin p)) := ⟨project,quotient_project.continuous⟩
  let g : C(Coordinates p,ℂ) := ⟨periodSum f,periodSum_continuous hc hf⟩
  have hq : IsQuotientMap q := quotient_project.isQuotientMap
  have hinv : Function.FactorsThrough g q := by
    intro x y h
    obtain ⟨k,rfl⟩ := shift_of_project_eq h
    change (∑' n : Indices p, f (y+grid k+grid n)) = ∑' n : Indices p, f (y+grid n)
    calc
      _ = ∑' n : Indices p, f (y+grid (k+n)) := by
        apply tsum_congr; intro n; congr 1; ext i; simp [grid,add_assoc]
      _ = _ := (Equiv.addLeft k).tsum_eq (fun n => f (y+grid n))
  exact ⟨hq.lift g hinv,fun x => congrArg (fun u : C(Coordinates p,ℂ) => u x) (hq.lift_comp g hinv)⟩

end
end HalfBall.Poisson
