module
public import HalfBall.Weights.CombRecovery
public import HalfBall.Converse
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall
open MeyerGeneralProblem.LevOlevskii Set FourierTransform
open scoped FourierTransform InnerProductSpace

/-- The inverse transform has the reflected spectral weights. -/
private theorem inverse_weights {p} {μ : TemperedDistribution (V p) ℂ} {B : Set (V p)} {b : B → ℂ}
    (hb : HasLocallyAtomicExpansion (𝓕 μ) B b) :
    HasLocallyAtomicExpansion (𝓕⁻ μ) (reflected B) (fun x => b ⟨-x.val,x.property⟩) := by
  let e : reflected B ≃ B :=
    { toFun := fun x => ⟨-x.val,x.property⟩
      invFun := fun x => ⟨-x.val,by simp [reflected]⟩
      left_inv := fun x => Subtype.ext (neg_neg x.val)
      right_inv := fun x => Subtype.ext (neg_neg x.val) }
  have dbl (φ : SchwartzMap (V p) ℂ) (x : V p) : 𝓕 (𝓕 φ) x = φ (-x) := by
    have h := congrArg (fun ψ : SchwartzMap (V p) ℂ => ψ (-x)) (fourierInv_fourier_eq (F := SchwartzMap (V p) ℂ) φ)
    change (𝓕 (𝓕 φ)) (- -x) = φ (-x) at h
    simpa only [neg_neg] using h
  refine ⟨fun x => hb.1 _,fun φ hc => ?_⟩
  let ψ := 𝓕 (𝓕 φ)
  have hcomp : HasCompactSupport (⇑ψ) := by
    rw [show ⇑ψ = (φ : V p → ℂ) ∘ Homeomorph.neg (V p) from funext (dbl φ)]
    exact hc.comp_homeomorph _
  have hi : (𝓕 μ) ψ = (𝓕⁻ μ) φ := by
    change μ (𝓕 (𝓕 (𝓕 φ))) = μ (𝓕⁻ φ)
    congr 1
    ext x
    exact dbl (𝓕 φ) x
  simpa [Function.comp_def,e,ψ,dbl,← hi] using e.hasSum_iff.mpr (hb.2 ψ hcomp)

private theorem weighted_combs_of_matrix_sum {p} {μ : TemperedDistribution (V p) ℂ}
    (h : IsFiniteModulatedLatticeCombSum μ) : WeightedLatticeCombs μ := by
  classical
  obtain ⟨m,t,v,c,T,hT,hs⟩ := h
  let e (i : Fin m) := (T i).toLinearEquiv' ((T i).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr (hT i))).invertible
  let L (i : Fin m) : LatticeCoset p := ⟨t i,(e i).toContinuousLinearEquiv.trans (PiLp.continuousLinearEquiv 2 ℝ _).symm⟩
  refine ⟨m,L,v,c,fun φ => ?_⟩
  let f (z : Fin m × (Fin p → ℤ)) := c z.1 * Poisson.phase ⟪v z.1,(L z.1).site z.2⟫_ℝ * φ ((L z.1).site z.2)
  have hh : HasSum f (μ φ) := hs φ
  rw [← hh.tsum_eq,hh.summable.tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  simp only [f,mul_assoc,tsum_mul_left]

/-- Appendix B. Unit-ball caps on the two locally finite actual carriers
force a finite sum of shifted, modulated full-rank lattice combs. -/
theorem weighted_combs_of_ball_caps {p M N} {μ : TemperedDistribution (V p) ℂ} {A B : Set (V p)}
    (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B) (hμ : LocalAtoms μ A)
    (hν : LocalAtoms (𝓕 μ) B) (cA : BallCap A M) (cB : BallCap B N) : WeightedLatticeCombs μ := by
  obtain ⟨fgA,fgB⟩ := both_carrier_groups_fg hA hB hμ hν cA cB
  obtain ⟨u,v⟩ := matrix_covers_of_finite_generation hA hB hμ hν cA cB fgA fgB
  obtain ⟨a,ha⟩ := hμ
  obtain ⟨b,hb⟩ := hν
  let ν := 𝓕⁻ μ
  have inv : 𝓕 ν = μ := fourier_fourierInv_eq μ
  have hr := inverse_weights hb
  have ha' : HasLocallyAtomicExpansion (𝓕 ν) A a := inv ▸ ha
  obtain ⟨C,hC⟩ := Weights.spectral_weights_bounded ha hb cB u v
  have hrB : Weights.BoundedRecord (fun x : reflected B => b ⟨-x.val,x.property⟩) :=
    ⟨latticeCovered_of_matrixCover (reflected_lattice_cover v),C,fun x => hC _⟩
  have hrA : Weights.BoundedRecord a := ⟨latticeCovered_of_matrixCover u,
    Weights.spectral_weights_bounded hr ha' cA (reflected_lattice_cover v) u⟩
  exact weighted_combs_of_matrix_sum (inv ▸ Weights.spectral_comb_of_lattice_covers hr hrB ha' hrA
    (reflected_lattice_cover v) u)

/-- Independent half-ball data on the two carriers force the comb representation. -/
theorem weighted_combs_of_half_balls {p} (hp : 0 < p) {μ : TemperedDistribution (V p) ℂ} {A B : Set (V p)}
    (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B)
    (ha : LocalAtoms μ A) (hb : LocalAtoms (𝓕 μ) B) :
    IndependentHalfBallData A B → WeightedLatticeCombs μ := by
  rintro ⟨ω,η,R,S,hω,hη,hR,hS⟩
  obtain ⟨M,hM⟩ := both_carriers_relatively_separated hp hA hB ha hb hω hη hR hS
  exact weighted_combs_of_ball_caps hA hB ha hb
    (ballCap_of_count A hA fun x => (hM x).1) (ballCap_of_count B hB fun x => (hM x).2)

end HalfBall
