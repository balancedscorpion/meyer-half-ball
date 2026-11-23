/-
Weight recovery adapted from AppendixA/LatticeAverages.lean, AppendixA/TransformedAverages.lean.
See LICENSES/lev-olevskii-lattice-cover-MIT.txt.
-/
module
public import HalfBall.Weights.Records
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Weights
open MeyerGeneralProblem.LevOlevskii

section
open Filter Set Matrix
open scoped Topology Matrix Classical

/-- Products of the dual averages restrict to intersections, including when
the intersection has lower rank or is empty. Convergence is tested on each
Schwartz function with the original complex weights. -/
theorem tendsto_latticeIntersection_on_test {d : ℕ} {ι : Type*} (J : Finset ι)
    (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ) (hT : ∀ j ∈ J, (T j).det ≠ 0)
    {A : Set (Space d)} {a : A → ℂ} {μ : TemperedDistribution (Space d) ℂ}
    (_hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (φ : SchwartzMap (Space d) ℂ) :
    Tendsto (fun N => ∑' x : A, (a x * φ x) * ∏ j ∈ J, latticeBoxAverage (t j) (T j) N x)
      atTop (𝓝 (∑' x : A, (⋂ j ∈ J, range (latticeSite (t j) (T j))).indicator
        (fun y => a x * φ y) x.val)) := by
  classical
  apply tendsto_tsum_of_dominated_convergence (summable_weights hA φ)
  · intro x
    have h := (tendsto_finsetProd J (fun j hj => tendsto_latticeBoxAverage (t j) (T j)
      (hT j hj) x.val)).const_mul (a x * φ x)
    by_cases hmem : ∀ j ∈ J, x.val ∈ range (latticeSite (t j) (T j))
    · simpa [Set.indicator_apply, Finset.prod_boole, hmem] using h
    · simpa [Set.indicator_apply, Finset.prod_boole, hmem] using h
  · apply Eventually.of_forall
    intro N x
    rw [norm_mul, norm_prod]
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_latticeBoxAverage_le_one ..

end

section
open Matrix Filter FourierTransform MeasureTheory
open scoped Topology FourierTransform RealInnerProductSpace Matrix Classical

/-- Any finite complex combination of physical characters gives exactly the
same combination of translated spectral tests. -/
theorem finite_modulation_on_fourier_test {d : ℕ} {ι : Type*} [Fintype ι]
    {μ : TemperedDistribution (Space d) ℂ} {A : Set (Space d)} {a : A → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (c : ι → ℂ) (u : ι → Space d) (φ : SchwartzMap (Space d) ℂ) :
    HasSum (fun x : A => (a x * (𝓕 φ) x) * ∑ i, c i * (frequencyPhase (u i) x : ℂ))
      (∑ i, c i * (𝓕 μ) ((SchwartzMap.compSubConstCLM ℂ (-(u i))) φ)) := by
  have h (i : ι) := ((global_expansion hμ hA).2
    (𝓕 ((SchwartzMap.compSubConstCLM ℂ (-(u i))) φ))).mul_left (c i)
  simp_rw [Finset.mul_sum]
  simpa only [fourier_test_add, TemperedDistribution.fourier_apply,
    mul_comm, mul_assoc, mul_left_comm] using hasSum_sum (s := Finset.univ) (fun i _ => h i)

/-- Fourier-side formula for the averaged physical record at finite box size. -/
theorem latticeBox_on_fourier_test {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BoundedRecord b)
    (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (φ : SchwartzMap (Space d) ℂ) :
    (∑' x : A, (a x * (𝓕 φ) x) * latticeBoxAverage t T N x) =
    ∑ q : Fin d → Fin (N + 1), boxCoefficient t T q * ∑' y : B, b y * φ (y.val + boxFrequency T q) := by
  have h := (finite_modulation_on_fourier_test hμ hA (boxCoefficient (N := N) t T)
    (boxFrequency T) φ).tsum_eq
  have hshift (u : Space d) : (𝓕 μ) ((SchwartzMap.compSubConstCLM ℂ (-u)) φ) =
      ∑' y : B, b y * φ (y.val + u) := by
    simpa [SchwartzMap.compSubConstCLM_apply] using
      ((global_expansion hν hB).2
        ((SchwartzMap.compSubConstCLM ℂ (-u)) φ)).tsum_eq.symm
  simpa only [hshift, latticeBoxAverage_expansion, sub_eq_add_neg, AddChar.map_add_eq_mul,
    Circle.coe_mul, boxCoefficient, mul_left_comm, mul_comm, mul_assoc] using h

/-- The Fourier transform of the restriction to a coset is the weak limit on
Schwartz tests of the explicit weighted translates of the original spectrum. -/
theorem spectral_box_limit_on_test {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BoundedRecord b)
    (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.det ≠ 0) (φ : SchwartzMap (Space d) ℂ) :
    Tendsto (fun N => ∑ q : Fin d → Fin (N + 1), boxCoefficient t T q *
      ∑' y : B, b y * φ (y.val + boxFrequency T q)) atTop
      (𝓝 (∑' x : A, (Set.range (latticeSite t T)).indicator (fun z => a x * (𝓕 φ) z) x.val)) := by
  simp_rw [← latticeBox_on_fourier_test hμ hA hν hB]
  simpa [Set.iInter_const] using tendsto_latticeIntersection_on_test ({()} : Finset Unit) (fun _ => t)
    (fun _ => T) (fun _ _ => hT) hμ hA (𝓕 φ)

/-- Spectral translates for a finite intersection have total absolute
weight one, also when the intersection has lower rank. Their limit is
the restricted distribution evaluated on the Fourier transform of the test. -/
theorem spectral_intersection_limit_on_test {d : ℕ} {ι : Type*} [Fintype ι]
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BoundedRecord b)
    (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ) (hT : ∀ j, (T j).det ≠ 0)
    (φ : SchwartzMap (Space d) ℂ) :
    Tendsto (fun N => ∑ q : IntersectionBox ι d N, intersectionCoefficient t T q *
      ∑' y : B, b y * φ (y.val + intersectionFrequency T q)) atTop
      (𝓝 (∑' x : A, (⋂ j, Set.range (latticeSite (t j) (T j))).indicator
        (fun z => a x * (𝓕 φ) z) x.val)) := by
  classical
  have h := tendsto_latticeIntersection_on_test Finset.univ t T (fun j _ => hT j) hμ hA (𝓕 φ)
  have hshift (u : Space d) : (𝓕 μ) ((SchwartzMap.compSubConstCLM ℂ (-u)) φ) =
      ∑' y : B, b y * φ (y.val + u) := by
    simpa [SchwartzMap.compSubConstCLM_apply] using
      ((global_expansion hν hB).2
        ((SchwartzMap.compSubConstCLM ℂ (-u)) φ)).tsum_eq.symm
  have heq (N : ℕ) := (finite_modulation_on_fourier_test hμ hA
    (intersectionCoefficient (N := N) t T) (intersectionFrequency T) φ).tsum_eq
  simp_rw [hshift, ← latticeIntersection_expansion] at heq
  simpa [heq, Set.iInter_const] using h

end

end HalfBall.Weights
