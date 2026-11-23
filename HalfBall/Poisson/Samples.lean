module

public import HalfBall.LatticeCount
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

/-- Every Schwartz test is absolutely summable along every translate of a
full-rank lattice, including arbitrary shifts of the sampling lattice. -/
theorem summable_lattice_samples {p} (L : LatticeCoset p) (φ : SchwartzMap (V p) ℂ) :
    Summable (fun n : Fin p → ℤ => ‖φ (L.site n)‖) := by
  classical
  let b := Pi.basisFun ℝ (Fin p)
  let H := Submodule.span ℤ (Set.range b)
  let : DiscreteTopology H := ZSpan.discreteTopology_pi_basisFun
  let embed (n : Fin p → ℤ) : H := ⟨fun i => (n i : ℝ),
    (b.mem_span_iff_repr_mem ℤ _).mpr (fun i => ⟨n i, by simp [b]⟩)⟩
  have hemb : Function.Injective embed := by
    intro n m h
    funext i
    exact Int.cast_injective (α := ℝ) (show ((n i:ℤ):ℝ) = m i from congrFun (congrArg Subtype.val h) i)
  let k := Module.finrank ℤ H + 1
  let ψ := (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.basis)
    (SchwartzMap.compSubConstCLM ℂ (-L.shift) φ)
  have hψ (n : Fin p → ℤ) : ψ (embed n).val = φ (L.site n) := by
    simp [ψ,SchwartzMap.compSubConstCLM_apply,LatticeCoset.site,embed,add_comm]
  let C := SchwartzMap.seminorm ℂ k 0 ψ
  have hs := (ZLattice.summable_norm_pow_inv H k (by dsimp [k]; omega)).comp_injective hemb
  refine Summable.of_norm_bounded_eventually (hs.mul_left C) ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : Fin p → ℤ)] with n hn
  have hzero : embed 0 = 0 := by ext i; simp [embed]
  have hpos : 0 < ‖embed n‖ := norm_pos_iff.mpr fun h => hn (hemb (h.trans hzero.symm))
  have hbound := SchwartzMap.le_seminorm ℂ k 0 ψ (embed n).val
  simp only [norm_iteratedFDeriv_zero,hψ] at hbound
  simp only [Real.norm_of_nonneg (norm_nonneg _), Function.comp_apply]
  change ‖φ (L.site n)‖ ≤ C * ‖embed n‖⁻¹ ^ k
  rw [inv_pow, ← div_eq_mul_inv,le_div_iff₀ (pow_pos hpos k),mul_comm]
  exact hbound

end HalfBall
