/-
Weight recovery adapted from AppendixA/RestrictedTransform.lean, AppendixA/ShrinkingTests.lean, AppendixA/RestrictedAtoms.lean, AppendixA/FullRankRestrictions.lean.
See LICENSES/lev-olevskii-lattice-cover-MIT.txt.
-/
module
public import HalfBall.Weights.Averages
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Weights
open MeyerGeneralProblem.LevOlevskii

section
open Set MeasureTheory Filter FourierTransform
open scoped Topology FourierTransform ENNReal NNReal Classical

private theorem restricted_hasSum {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (_hμ : HasLocallyAtomicExpansion μ A a)
    (hA : BoundedRecord a) (D : Set (Space d)) (φ : SchwartzMap (Space d) ℂ) :
    HasSum (fun x : A => D.indicator (fun z => a x * (𝓕 φ) z) x.val)
      (restrictedFourierValue a D φ) := by
  apply Summable.hasSum
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (summable_weights hA (𝓕 φ))
  intro x
  by_cases hx : x.val ∈ D
  · simp [hx]
  · simpa only [Set.indicator_of_notMem hx, norm_zero] using norm_nonneg (a x * (𝓕 φ) x)

/-- Restricting in physical space and testing the transform is complex-linear
in the spectral test. -/
def restrictedFourierLinear {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : BoundedRecord a) (D : Set (Space d)) : SchwartzMap (Space d) ℂ →ₗ[ℂ] ℂ where
  toFun := restrictedFourierValue a D
  map_add' φ ψ := by
    apply (restricted_hasSum hμ hA D _).unique
    apply ((restricted_hasSum hμ hA D φ).add (restricted_hasSum hμ hA D ψ)).congr_fun
    intro x
    by_cases hx : x.val ∈ D <;> simp [hx, mul_add]
  map_smul' c φ := by
    apply (restricted_hasSum hμ hA D _).unique
    apply ((restricted_hasSum hμ hA D φ).mul_left c).congr_fun
    intro x
    by_cases hx : x.val ∈ D <;> simp [hx, mul_left_comm]

/-- Translating a spectral test along a frequency which is constant on the
physical restriction multiplies its value by that phase. -/
theorem restrictedFourierValue_translate {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : BoundedRecord a) (D : Set (Space d)) (u : Space d) (z : Circle)
    (hz : ∀ x ∈ D, frequencyPhase u x = z) (φ : SchwartzMap (Space d) ℂ) :
    restrictedFourierValue a D ((SchwartzMap.compSubConstCLM ℂ (-u)) φ) =
      (z : ℂ) * restrictedFourierValue a D φ := by
  apply (restricted_hasSum hμ hA D _).unique
  apply ((restricted_hasSum hμ hA D φ).mul_left (z : ℂ)).congr_fun
  intro x
  by_cases hx : x.val ∈ D
  · simp [hx, fourier_test_add, hz x.val hx, mul_left_comm]
  · simp [hx]

/-- Inclusion–exclusion on any finite physical cover recovers the original
spectral test value, including all cancellations at overlapping sites. -/
theorem fourierValue_inclusion_exclusion {d : ℕ} {ι : Type*}
    {μ : TemperedDistribution (Space d) ℂ} {A : Set (Space d)} {a : A → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (J : Finset ι) (D : ι → Set (Space d)) (hcover : A ⊆ ⋃ j ∈ J, D j)
    (φ : SchwartzMap (Space d) ℂ) :
    (𝓕 μ) φ = ∑ S ∈ J.powerset with S.Nonempty,
      ((-1 : ℤ) ^ (S.card + 1)) • restrictedFourierValue a (⋂ j ∈ S, D j) φ := by
  apply ((global_expansion hμ hA).2 (𝓕 φ)).unique
  apply (hasSum_sum (s := J.powerset.filter Finset.Nonempty)
    (fun S _ => (restricted_hasSum hμ hA (⋂ j ∈ S, D j) φ).const_smul ((-1 : ℤ) ^ (S.card + 1)))).congr_fun
  intro x
  simpa only [Set.indicator_of_mem (hcover x.property)] using
    J.indicator_biUnion_eq_sum_powerset D (fun z => a x * (𝓕 φ) z) x.val

/-- Uniform bound on the transformed restrictions as functionals on compact
tests bounded by one in balls of radius `r`. -/
theorem restrictedTransform_local_bound {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BoundedRecord b) (r : ℝ) :
    ∃ M : ℝ≥0, ∀ {ι : Type} [Fintype ι] (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ),
      (∀ j, (T j).det ≠ 0) → ∀ c : Space d, ∀ φ : SchwartzMap (Space d) ℂ,
      (∀ z, ‖φ z‖ ≤ 1) → (∀ z, φ z ≠ 0 → dist z c ≤ r) →
      ‖restrictedFourierValue a (⋂ j, range (latticeSite (t j) (T j))) φ‖ ≤ M := by
  obtain ⟨M, hM⟩ := joint_variation hA hB r
  refine ⟨M, fun {ι} _ t T hT c φ hφ hsupp => ?_⟩
  apply le_of_tendsto' (spectral_intersection_limit_on_test hμ hA hν hB t T hT φ).norm
  intro N
  calc
    _ ≤ ∑ q : IntersectionBox ι d N, ‖intersectionCoefficient t T q‖ * M := by
      apply norm_sum_le_of_le
      intro q _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (translated_sum_ball_bound b r M (fun p => (hM p).2) φ c hφ hsupp _) (norm_nonneg _)
    _ = M := by rw [← Finset.sum_mul, intersectionCoefficient_norm_sum, one_mul]

end

section
open Filter Set Metric FourierTransform
open scoped Topology FourierTransform ContDiff Classical NNReal

/-- Fourier transforms of physical restrictions to finite lattice
intersections have well-defined coefficients at every spectral point. -/
theorem restrictedFourierLinear_hasLocalTestBounds {d : ℕ} {ι : Type} [Fintype ι]
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BoundedRecord b)
    (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ) (hT : ∀ j, (T j).det ≠ 0) :
    HasLocalTestBounds (restrictedFourierLinear hμ hA (⋂ j, range (latticeSite (t j) (T j)))) := by
  intro r
  obtain ⟨M, hM⟩ := restrictedTransform_local_bound hμ hA hν hB r
  exact ⟨M, hM t T hT⟩

end

section
open Set Filter FourierTransform
open scoped Topology FourierTransform RealInnerProductSpace

/-- The coefficient at a translated frequency acquires the same phase as
the translated test when the physical character is constant on `D`. -/
theorem restrictedAtom_translate {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : BoundedRecord a) (D : Set (Space d)) (hL : HasLocalTestBounds (restrictedFourierLinear hμ hA D))
    (u : Space d) (z : Circle) (hz : ∀ y ∈ D, frequencyPhase u y = z) (x : Space d) :
    testAtom (restrictedFourierLinear hμ hA D) (x - u) =
      (z : ℂ) * testAtom (restrictedFourierLinear hμ hA D) x := by
  apply tendsto_nhds_unique (tendsto_testAtom hL (x - u))
  apply ((tendsto_testAtom hL x).const_mul (z : ℂ)).congr
  intro n
  have ht : (SchwartzMap.compSubConstCLM ℂ (-u)) (atomTest n x) = atomTest n (x - u) := by
    ext y
    simp only [SchwartzMap.compSubConstCLM_apply, atomTest_apply, atomProfile]
    congr 1
    congr 1
    abel
  exact ht ▸ (restrictedFourierValue_translate hμ hA D u z hz (atomTest n x)).symm

/-- When the physical restriction lies in a proper affine hyperplane, its
Fourier transform has zero extracted coefficient at every spectral point. -/
theorem restrictedAtom_zero_of_hyperplane {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : BoundedRecord a) (D : Set (Space d)) (hL : HasLocalTestBounds (restrictedFourierLinear hμ hA D))
    (v : Space d) (hv : v ≠ 0) (k : ℝ) (hk : ∀ y ∈ D, inner ℝ v y = k) (x : Space d) :
    testAtom (restrictedFourierLinear hμ hA D) x = 0 := by
  let := Icc.infinite (show (0 : ℝ) < 1 by norm_num)
  let s : Icc (0 : ℝ) 1 ↪ Space d :=
    ⟨fun t => x - t.val • v, fun _ _ h => Subtype.ext (smul_left_injective ℝ hv (sub_right_inj.mp h))⟩
  apply testAtom_zero_of_equal_orbit hL s x ‖v‖
  · intro t
    change dist (x - t.val • v) x ≤ ‖v‖
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    exact mul_le_of_le_one_left (norm_nonneg _) t.property.2
  · intro t
    have hz (y) (hy : y ∈ D) : frequencyPhase (t.val • v) y = Real.fourierChar (t.val * k) := by
      simp [frequencyPhase, hk y hy]
    change ‖testAtom _ (x - t.val • v)‖ = _
    simpa only [norm_mul, Circle.norm_coe, one_mul] using congrArg norm (restrictedAtom_translate hμ hA D hL (t.val • v) _ hz x)

/-- Every actual spectral coefficient, extended by zero off the spectrum,
is the signed sum of the coefficients of the nonempty physical restrictions. -/
theorem recordWeight_inclusion_exclusion {d : ℕ} {ι : Type} [DecidableEq ι]
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BoundedRecord b)
    (J : Finset ι) (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ)
    (hT : ∀ j ∈ J, (T j).det ≠ 0) (hcover : A ⊆ ⋃ j ∈ J, range (latticeSite (t j) (T j)))
    (x : Space d) :
    recordWeight b x = ∑ S ∈ J.powerset with S.Nonempty, ((-1 : ℤ) ^ (S.card + 1)) •
      testAtom (restrictedFourierLinear hμ hA (⋂ j ∈ S, range (latticeSite (t j) (T j)))) x := by
  classical
  let D (j : ι) := range (latticeSite (t j) (T j))
  have hbounded (S : Finset ι) (hS : S ⊆ J) :
      HasLocalTestBounds (restrictedFourierLinear hμ hA (⋂ j ∈ S, D j)) := by
    simpa only [D, iInter_subtype] using restrictedFourierLinear_hasLocalTestBounds hμ hA hν hB
      (fun j : S => t j.val) (fun j : S => T j.val) (fun j => hT j.val (hS j.property))
  have h := tendsto_finsetSum (J.powerset.filter Finset.Nonempty) (fun S hS =>
    (tendsto_testAtom (hbounded S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)) x).const_smul
      ((-1 : ℤ) ^ (S.card + 1)))
  apply tendsto_nhds_unique _ h
  apply tendsto_const_nhds.congr'
  filter_upwards [atom_test_weight hν hB x] with n hn
  exact hn.symm.trans (fourierValue_inclusion_exclusion hμ hA J D hcover (atomTest n x))

end

section
open Set Filter FourierTransform
open scoped Topology FourierTransform

/-- Given a finite physical lattice cover, the entire spectral coefficient
function is a finite integer combination of coefficient functions of
full-rank single-coset restrictions. This includes points off the spectrum. -/
theorem spectral_weights_from_fullRank_restrictions {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BoundedRecord b)
    (hcover : HasFiniteLatticeCover A) :
    ∃ (m : ℕ) (c : Fin m → ℤ) (t : Fin m → Space d) (T : Fin m → Matrix (Fin d) (Fin d) ℝ),
      (∀ j, (T j).det ≠ 0) ∧ ∀ x, recordWeight b x =
      ∑ j, c j • testAtom (restrictedFourierLinear hμ hA (range (latticeSite (t j) (T j)))) x := by
  classical
  obtain ⟨m, _, t, T, hT, hcover⟩ := hcover
  let D (j : Fin m) := range (latticeSite (t j) (T j))
  let J := (Finset.univ : Finset (Fin m)).powerset.filter Finset.Nonempty
  let I (S : J) := ⋂ j ∈ S.val, D j
  have hI (S : J) : I S = ⋂ j : S.val, range (latticeSite (t j.val) (T j.val)) := by
    simp [I, D, iInter_subtype]
  have hlocal (S : J) : HasLocalTestBounds (restrictedFourierLinear hμ hA (I S)) := by
    rw [hI]
    exact restrictedFourierLinear_hasLocalTestBounds hμ hA hν hB _ _ (fun j => hT j.val)
  have split (S : J) : ∃ (k : ℤ) (p : Space d) (U : Matrix (Fin d) (Fin d) ℝ),
      U.det ≠ 0 ∧ ∀ x, ((-1 : ℤ) ^ (S.val.card + 1)) • testAtom (restrictedFourierLinear hμ hA (I S)) x =
        k • testAtom (restrictedFourierLinear hμ hA (range (latticeSite p U))) x := by
    by_cases hne : (I S).Nonempty
    · obtain ⟨j, hj⟩ := (Finset.mem_filter.mp S.property).2
      let : Nonempty S.val := ⟨⟨j, hj⟩⟩
      obtain ⟨p, hp⟩ := hne
      rw [hI, mem_iInter] at hp
      obtain ⟨U, hU, heq⟩ | ⟨v, hv, hflat⟩ :=
        latticeIntersection_lattice_or_hyperplane _ _ (fun j : S.val => hT j.val) p hp
      · exact ⟨_, p, U, hU, fun x => by rw [hI, heq]⟩
      · refine ⟨0, 0, 1, by simp, fun x => ?_⟩
        rw [restrictedAtom_zero_of_hyperplane hμ hA (I S) (hlocal S) v hv _ (hI S ▸ hflat), smul_zero, zero_smul]
    · have hemp := Set.not_nonempty_iff_eq_empty.mp hne
      have hz (x : Space d) : testAtom (restrictedFourierLinear hμ hA (I S)) x = 0 := by
        apply tendsto_nhds_unique (tendsto_testAtom (hlocal S) x)
        simp only [hemp]
        simp [restrictedFourierLinear, restrictedFourierValue]
      exact ⟨0, 0, 1, by simp, fun x => by rw [hz, smul_zero, zero_smul]⟩
  choose k p U hU hcoeff using split
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J, k ∘ e.symm, p ∘ e.symm, U ∘ e.symm, fun j => hU _, fun x => ?_⟩
  have hcov : A ⊆ ⋃ j ∈ (Finset.univ : Finset (Fin m)), D j := by
    intro y hy
    obtain ⟨j, z, hz⟩ := hcover y hy
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_univ _, z, hz.symm⟩⟩
  rw [recordWeight_inclusion_exclusion hμ hA hν hB Finset.univ t T (fun j _ => hT j) hcov x]
  change (∑ S ∈ J, _) = _
  rw [← Finset.sum_attach J]
  change (∑ S : J, ((-1 : ℤ) ^ (S.val.card + 1)) • testAtom (restrictedFourierLinear hμ hA (I S)) x) = _
  simp_rw [hcoeff]
  exact (e.symm.sum_comp _).symm

end

end HalfBall.Weights
