module
public import HalfBall.Weights.Isolation
public import AppendixA.DualCosets
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall.Weights
open MeyerGeneralProblem.LevOlevskii Set Metric Filter FourierTransform Finset
open scoped FourierTransform Topology InnerProductSpace

/-- Any trigonometric polynomial vanishing on the physical carrier
annihilates the spectral coefficient record by the corresponding finite
sum of shifts. This uses local atomic expansions on compact tests. -/
theorem spectral_weight_relation {p M} {μ : TemperedDistribution (V p) ℂ}
    {A B : Set (V p)} {a : A → ℂ} {b : B → ℂ}
    (ha : HasLocallyAtomicExpansion μ A a) (hb : HasLocallyAtomicExpansion (𝓕 μ) B b)
    (cap : BallCap B M) {ι : Type*} [Fintype ι] (u : ι → V p) (c : ι → ℂ)
    (hP : ∀ x ∈ A, characterSum u c x = 0) (y : V p) :
    ∑ i, c i * recordWeight b (y-u i) = 0 := by
  classical
  let W := shiftedSpectrum (𝓕 μ) u c
  let E := shiftedSites B u
  let w (z : E) := ∑ i, c i * recordWeight b (z.val-u i)
  have hc0 (φ : SchwartzMap (V p) ℂ) (hc : HasCompactSupport φ) : (𝓕 W) φ = 0 := by
    have hz (z : A) := hP z z.property
    simpa [hz] using (shiftedSpectrum_transform ha u c φ hc).tsum_eq.symm
  have hW : 𝓕 W = 0 := by
    ext1 φ
    obtain ⟨ψ,hc,_,_,ht⟩ := exists_bounded_compact_schwartz_approximation φ
    exact tendsto_nhds_unique ((𝓕 W).continuous.continuousAt.tendsto.comp ht)
      (tendsto_const_nhds.congr (fun n => (hc0 _ (hc n)).symm))
  by_cases hy : y ∈ E
  · let i : E := ⟨y,hy⟩
    obtain ⟨R,_,hiso⟩ := isolated_window_of_ballCap p (Fintype.card ι*M)
    obtain ⟨φ,_,hφ,hz⟩ := hiso E (shiftedSites_cap cap u) y
    have hh := evaluate_isolated_site (T := W) (a := w) (shiftedSpectrum_atoms hb u c) i (𝓕 φ)
      (fun z hn => hz z z.property (fun h => hn (Subtype.ext h)))
    change (𝓕 W) φ = w i * (𝓕 φ) y at hh
    simpa [hW,hφ,w,i] using hh.symm
  · apply sum_eq_zero; intro i _
    have h : y-u i ∉ B := fun hz => hy ⟨i,hz⟩
    simp [recordWeight,h]

/-- Taking one dual-lattice displacement per physical coset gives a
recurrence with a nonzero coefficient on the unshifted spectral weight. -/
theorem lattice_annihilator {p M m} {μ : TemperedDistribution (V p) ℂ}
    {A B : Set (V p)} {a : A → ℂ} {b : B → ℂ}
    (ha : HasLocallyAtomicExpansion μ A a) (hb : HasLocallyAtomicExpansion (𝓕 μ) B b)
    (cap : BallCap B M) (t : Fin m → V p) (T : Fin m → Matrix (Fin p) (Fin p) ℝ)
    (hT : ∀ i, (T i).det ≠ 0) (hc : ∀ x ∈ A, ∃ i, x ∈ range (latticeSite (t i) (T i)))
    (v : Fin m → V p) (hv : ∀ i, v i ∈ matrixLattice (dualMatrix (T i))) :
    ∃ c : Finset (Fin m) → ℂ, c ∅ ≠ 0 ∧ ∀ y : V p,
      ∑ J, c J * recordWeight b (y-∑ i ∈ J,v i) = 0 := by
  classical
  let z (i : Fin m) := (frequencyPhase (v i) (t i) : ℂ)
  let c (J : Finset (Fin m)) := ∏ i ∈ Jᶜ, -z i
  refine ⟨c,by simp [c,z,Finset.prod_ne_zero_iff,Circle.coe_ne_zero],fun y => ?_⟩
  apply spectral_weight_relation ha hb cap (fun J : Finset (Fin m) => ∑ i ∈ J,v i) c _ y
  intro x hx
  obtain ⟨i,hi⟩ := hc x hx
  have hz := dual_phase_on_lattice (t i) (T i) (hT i) (v i) (hv i) x hi
  have hprod : ∏ j, ((frequencyPhase (v j) x : ℂ) + -z j) = 0 := prod_eq_zero (mem_univ i) (by simp [z,hz])
  have hchar (J : Finset (Fin m)) : (frequencyPhase (∑ j ∈ J,v j) x : ℂ) = ∏ j ∈ J,(frequencyPhase (v j) x : ℂ) := by
    change (Real.fourierChar ⟪x,∑ j ∈ J,v j⟫_ℝ : ℂ) = _
    induction J using Finset.induction_on with
    | empty => simp
    | insert j J hj ih =>
      rw [sum_insert hj,inner_add_right,AddChar.map_add_eq_mul,Circle.coe_mul,prod_insert hj,ih]
      rfl
  simpa only [Fintype.prod_add,mul_comm,c,characterSum,hchar] using hprod

end HalfBall.Weights
