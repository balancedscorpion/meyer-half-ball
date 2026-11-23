module

public import HalfBall.Poisson.Periodization
import Mathlib.Tactic

@[expose] public section
namespace HalfBall.Poisson

open Filter MeasureTheory Set Topology UnitAddTorus
open scoped Topology

variable {p : ℕ}

private def cell (n : Indices p) : Set (Coordinates p) :=
  {x | ∀ i, x i ∈ Ioc (n i : ℝ) ((n i : ℝ)+1)}

private theorem cell_measurable (n : Indices p) : MeasurableSet (cell n) :=
  MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)

private theorem in_cell {n : Indices p} {x : Coordinates p} :
    x ∈ cell n ↔ ∀ i, ⌈x i⌉ = n i + 1 := by
  simp [cell,Int.ceil_eq_iff]

private theorem cells_disjoint : Pairwise (fun i j : Indices p => Disjoint (cell i) (cell j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hj
  apply hij; funext k
  have h := (in_cell.mp hx k).symm.trans (in_cell.mp hj k)
  omega

private theorem cells_cover : (⋃ n : Indices p, cell n) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨fun i => ⌈x i⌉-1,in_cell.mpr (fun i => by simp)⟩

private theorem cell_translate (n : Indices p) :
    (fun x : Coordinates p => x+grid n) ⁻¹' cell n = cell 0 := by
  ext x
  simp [cell,grid,add_comm (x _) (↑(n _):ℝ)]

private theorem integral_periodSum {f : Coordinates p → ℂ} (hc : Continuous f)
    (hf : HasCompactSupport f) :
    ∫ x in cell 0, periodSum f x = ∫ x, f x := by
  classical
  obtain ⟨F,hF⟩ := finite_shifts hf 1
  have hnorm {x : Coordinates p} (hx : x ∈ cell 0) : ‖x‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    have hi := hx i
    simp only [Pi.zero_apply,Int.cast_zero,zero_add,mem_Ioc] at hi
    simpa [Real.norm_eq_abs,abs_of_pos hi.1] using hi.2
  let I (n : Indices p) := ∫ x in cell 0, f (x+grid n)
  have hI (n) : I n = ∫ x in cell n, f x := by
    have he := (measurePreserving_add_right (volume : Measure (Coordinates p)) (grid n)).setIntegral_preimage_emb
      (MeasurableEquiv.addRight (grid n)).measurableEmbedding f (cell n)
    rwa [cell_translate] at he
  have hsum : HasSum I (∫ x, f x) := by
    have hh := hasSum_integral_iUnion (μ := volume) (@cell_measurable p) cells_disjoint
      (hc.integrable_of_hasCompactSupport hf).integrableOn
    rw [cells_cover,setIntegral_univ] at hh
    simpa only [funext hI] using hh
  have hzero (n) (hn : n ∉ F) : I n = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact hF x (hnorm hx) n hn
  calc
    _ = ∫ x in cell 0, ∑ n ∈ F, f (x+grid n) := by
      apply setIntegral_congr_fun (cell_measurable _)
      intro x hx
      exact (hasSum_sum_of_ne_finset_zero (hF x (hnorm hx))).tsum_eq
    _ = ∑ n ∈ F, I n := by
      apply integral_finsetSum
      intro n _
      have he := (measurePreserving_add_right (volume : Measure (Coordinates p)) (grid n)).integrable_comp_emb
        (MeasurableEquiv.addRight (grid n)).measurableEmbedding (g := f)
      exact (he.mpr (hc.integrable_of_hasCompactSupport hf)).integrableOn
    _ = _ := (hasSum_sum_of_ne_finset_zero hzero).unique hsum

/-- The coefficient of a periodized compact test is its Fourier integral
over all of Euclidean space. -/
theorem periodization_coeff {f : Coordinates p → ℂ} (hc : Continuous f) (hf : HasCompactSupport f)
    (P : C(UnitAddTorus (Fin p),ℂ)) (hP : ∀ x, P (project x) = periodSum f x) (n : Indices p) :
    mFourierCoeff P n = ∫ x, mFourier (-n) (project x) * f x := by
  let g (x : Coordinates p) := mFourier (-n) (project x) * f x
  have hg : Continuous g := ((mFourier (-n)).continuous.comp
    (by exact continuous_pi (fun _ => continuous_quotient_mk'.comp (continuous_apply _)) : Continuous project)).mul hc
  have hgc : HasCompactSupport g := hf.mul_left
  rw [mFourierCoeff, integral_preimage _ (0 : Coordinates p)]
  have hcell : {x : Coordinates p | ∀ i, x i ∈ Ioc ((0 : Coordinates p) i) (((0 : Coordinates p) i) + 1)} = cell 0 := by simp [cell]
  rw [hcell]
  change (∫ x in cell 0, mFourier (-n) (project x) • P (project x)) = _
  rw [← integral_periodSum hg hgc]
  apply setIntegral_congr_fun (cell_measurable _)
  intro x _
  change mFourier (-n) (project x) * P (project x) = periodSum g x
  rw [hP,periodSum,← tsum_mul_left]
  apply tsum_congr
  intro k
  simp [g,project_add_grid]

/-- Poisson summation on the standard integer lattice in arbitrary finite
dimension, for compact continuous tests with summable Fourier samples. -/
theorem poisson_compact {f : Coordinates p → ℂ} (hc : Continuous f) (hf : HasCompactSupport f)
    (hs : Summable (fun n : Indices p => ∫ x, mFourier (-n) (project x) * f x))
    (y : Coordinates p) :
    HasSum (fun n : Indices p => (∫ x, mFourier (-n) (project x) * f x) *
      mFourier n (project y)) (∑' n : Indices p, f (y+grid n)) := by
  obtain ⟨P,hP⟩ := exists_periodization hc hf
  have hcoef := periodization_coeff hc hf P hP
  have h := hasSum_mFourier_series_apply_of_summable (f := P)
    (by simpa only [funext hcoef] using hs) (project y)
  simpa only [hcoef,smul_eq_mul,hP,periodSum] using h

end HalfBall.Poisson
