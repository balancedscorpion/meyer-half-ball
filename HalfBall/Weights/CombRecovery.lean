/-
Weight recovery adapted from AppendixA/DualCosets.lean, AppendixA/CombWeights.lean, AppendixA/FiniteDualClasses.lean.
See LICENSES/lev-olevskii-lattice-cover-MIT.txt.
-/
module
public import HalfBall.Weights.Restrictions
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Weights
open MeyerGeneralProblem.LevOlevskii

section
open Set Matrix FourierTransform
open scoped Matrix FourierTransform RealInnerProductSpace Classical

/-- On every dual-lattice translate the atom function is one fixed
modulation, with an amplitude determined by any one representative. -/
theorem restrictedAtom_on_dual_coset {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : BoundedRecord a) (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.det ≠ 0)
    (hL : HasLocalTestBounds (restrictedFourierLinear hμ hA (range (latticeSite t T))))
    (p y : Space d) (hy : y ∈ range (latticeSite p (dualMatrix T))) :
    let F := testAtom (restrictedFourierLinear hμ hA (range (latticeSite t T)))
    F y = (F p * (frequencyPhase t p : ℂ)) * (frequencyPhase (-t) y : ℂ) := by
  have hu := (matrixLattice (dualMatrix T)).neg_mem ((mem_latticeCoset_iff ..).mp hy)
  rw [neg_sub] at hu
  have h := restrictedAtom_translate hμ hA _ hL (p-y) _
    (dual_phase_on_lattice t T hT _ hu) p
  rw [sub_sub_cancel] at h
  have hph : frequencyPhase (p-y) t = frequencyPhase t p * frequencyPhase (-t) y := by
    simp [frequencyPhase, real_inner_comm p t,
      real_inner_comm y t, AddChar.map_sub_eq_div, AddChar.map_neg_eq_inv, div_eq_mul_inv]
  simpa only [hph, Circle.coe_mul, mul_assoc, mul_comm, mul_left_comm] using h

/-- Finitely many nonzero classes modulo the dual lattice give an explicit
finite sum of modulated coset indicators for this restriction. -/
theorem restrictedAtom_comb_of_finite_classes {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : BoundedRecord a) (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.det ≠ 0)
    (hL : HasLocalTestBounds (restrictedFourierLinear hμ hA (range (latticeSite t T)))) :
    let F := testAtom (restrictedFourierLinear hμ hA (range (latticeSite t T)))
    let H := matrixLattice (dualMatrix T)
    (H.mkQ '' Function.support F).Finite →
      ∃ (m : ℕ) (p : Fin m → Space d) (c : Fin m → ℂ), ∀ y, F y =
        ∑ j, (range (latticeSite (p j) (dualMatrix T))).indicator
          (fun z => c j * (frequencyPhase (-t) z : ℂ)) y := by
  intro F H hfin
  let S := H.mkQ '' Function.support F
  let := hfin.fintype
  choose pick _ hpick using fun q : S => q.property
  let e := Fintype.equivFin S
  let c (q : S) := F (pick q) * (frequencyPhase t (pick q) : ℂ)
  let D (q : S) := range (latticeSite (pick q) (dualMatrix T))
  have hclass (q : S) (y : Space d) : y ∈ D q ↔ H.mkQ y = q.val := by
    rw [← hpick q, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_latticeCoset_iff]
  refine ⟨Fintype.card S, pick ∘ e.symm, c ∘ e.symm, fun y => ?_⟩
  change F y = ∑ j, (D (e.symm j)).indicator (fun z => c (e.symm j) * _) y
  rw [e.symm.sum_comp (fun q => (D q).indicator (fun z => c q * (frequencyPhase (-t) z : ℂ)) y)]
  by_cases h : H.mkQ y ∈ S
  · let q : S := ⟨H.mkQ y, h⟩
    have hy : y ∈ D q := (hclass q y).mpr rfl
    rw [Finset.sum_eq_single q, Set.indicator_of_mem hy]
    · exact restrictedAtom_on_dual_coset hμ hA t T hT hL (pick q) y hy
    · intro j _ hj
      exact Set.indicator_of_notMem (fun hmem => hj (Subtype.ext ((hclass j y).mp hmem).symm)) _
    · simp
  · have hzero : F y = 0 := by
      by_contra hy
      exact h ⟨y, hy, rfl⟩
    rw [hzero]
    symm
    exact Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem
      (fun hy => h (((hclass j y).mp hy).symm ▸ j.property)) _

end

section
open Set Filter Metric FourierTransform
open scoped Matrix FourierTransform RealInnerProductSpace Classical

private theorem summable_schwartz_on_sites {d : ℕ} {D : Set (Space d)} (hD : UniformlyDiscrete D)
    (φ : SchwartzMap (Space d) ℂ) : Summable (fun z : D => ‖φ z‖) := by
  let k := d+1
  let C := 2^k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((summable_inverse_weight hD k (by omega)).mul_left C)
  intro x
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  simpa only [norm_iteratedFDeriv_zero] using
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl φ x.val

/-- An identity of coefficient functions on the whole ambient space, with
the atomic record extended by zero, gives the unordered distributional sum
even for intersecting or incommensurate lattices. -/
theorem latticeCombSum_of_recordWeight {d m : ℕ} {ν : TemperedDistribution (Space d) ℂ}
    {B : Set (Space d)} {b : B → ℂ} (hν : HasLocallyAtomicExpansion ν B b) (hB : BoundedRecord b)
    (t s : Fin m → Space d) (c : Fin m → ℂ) (T : Fin m → Matrix (Fin d) (Fin d) ℝ)
    (hT : ∀ j, (T j).det ≠ 0)
    (hw : ∀ y, recordWeight b y = ∑ j, (range (latticeSite (t j) (T j))).indicator
      (fun z => c j * (frequencyPhase (s j) z : ℂ)) y) :
    IsFiniteModulatedLatticeCombSum ν := by
  refine ⟨m, t, s, c, T, hT, fun φ => ?_⟩
  let D j := range (latticeSite (t j) (T j))
  let f j (z : Space d) := (c j * (frequencyPhase (s j) z : ℂ)) * φ z
  let g j := (D j).indicator (f j)
  have hs (j) : Summable (fun z : D j => ‖f j z‖) := by
    simpa [f, norm_mul] using (summable_schwartz_on_sites (latticeCoset_uniformlyDiscrete _ _ (hT j)) φ).mul_left ‖c j‖
  let M j := ∑' z : D j, f j z
  have hD (j) : HasSum (g j) (M j) := hasSum_subtype_iff_indicator.mp (hs j).of_norm.hasSum
  have hatom : HasSum (fun z : Space d => recordWeight b z * φ z) (ν φ) := by
    have h := (global_expansion hν hB).2 φ
    apply (hasSum_subtype_iff_of_support_subset (s := B) (by
      intro x hx; by_contra hnot; exact hx (by simp [recordWeight, hnot]))).mp
    simpa [Function.comp_def, recordWeight] using h
  have hval : ν φ = ∑ j, M j := by
    apply hatom.unique
    apply (hasSum_sum (fun j (_ : j ∈ Finset.univ) => hD j)).congr_fun
    intro z
    rw [hw, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    change (D j).indicator _ z * φ z = (D j).indicator (f j) z
    by_cases hz : z ∈ D j <;> simp [hz, f]
  let term (p : Fin m × (Fin d → ℤ)) := f p.1 (latticeSite (t p.1) (T p.1) p.2)
  have hn (j) : Summable (fun z => ‖term (j,z)‖) := by
    let e := Equiv.ofInjective _ (latticeSite_injective (t j) (T j) (hT j))
    exact (e.summable_iff (f := fun z : D j => ‖f j z‖)).mpr (hs j)
  have hsum : Summable term :=
    ((summable_prod_of_nonneg (f := fun p => ‖term p‖) (fun _ => norm_nonneg _)).mpr
      ⟨hn, (hasSum_fintype _).summable⟩).of_norm
  have hrows (j) : HasSum (fun z => term (j,z)) (M j) :=
    ((latticeSite_injective (t j) (T j) (hT j)).hasSum_range_iff (f := f j)).mp (hs j).of_norm.hasSum
  have hall := hsum.hasSum.prod_fiberwise hrows
  have heq := hall.unique (hasSum_fintype M)
  rw [hval, ← heq]
  apply hsum.hasSum.congr_fun
  intro p
  simp [term, f, frequencyPhase]

/-- Once a physical cover and the finiteness of the dual classes for each
single-coset restriction are established, the original spectral distribution
is a finite sum of full-rank translated modulated combs. -/
theorem spectral_comb_of_finite_dual_classes {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BoundedRecord b) (hcover : HasFiniteLatticeCover A)
    (hclasses : ∀ (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ), T.det ≠ 0 →
      ((matrixLattice (dualMatrix T)).mkQ '' Function.support (testAtom
        (restrictedFourierLinear hμ hA (range (latticeSite t T))))).Finite) :
    IsFiniteModulatedLatticeCombSum (𝓕 μ) := by
  obtain ⟨m, k, t, T, hT, hweights⟩ := spectral_weights_from_fullRank_restrictions hμ hA hν hB hcover
  let F j := testAtom (restrictedFourierLinear hμ hA (range (latticeSite (t j) (T j))))
  have hlocal (j) : HasLocalTestBounds (restrictedFourierLinear hμ hA (range (latticeSite (t j) (T j)))) := by
    simpa [Set.iInter_const] using restrictedFourierLinear_hasLocalTestBounds hμ hA hν hB
      (fun _ : Unit => t j) (fun _ => T j) (fun _ => hT j)
  choose l p c hrow using fun j => restrictedAtom_comb_of_finite_classes hμ hA (t j) (T j) (hT j)
    (hlocal j) (hclasses (t j) (T j) (hT j))
  let I := (j : Fin m) × Fin (l j)
  let e := Fintype.equivFin I
  let center (i : I) := p i.1 i.2
  let scalar (i : I) := (k i.1 : ℂ) * c i.1 i.2
  let matrix (i : I) := dualMatrix (T i.1)
  let modulate (i : I) := -t i.1
  apply latticeCombSum_of_recordWeight hν hB (center ∘ e.symm) (modulate ∘ e.symm)
    (scalar ∘ e.symm) (matrix ∘ e.symm) (fun i => dualMatrix_det_ne_zero _ (hT (e.symm i).1))
  intro y
  let term (i : I) := (range (latticeSite (center i) (matrix i))).indicator
    (fun z => scalar i * (frequencyPhase (modulate i) z : ℂ)) y
  change recordWeight b y = ∑ j, term (e.symm j)
  rw [e.symm.sum_comp term, Fintype.sum_sigma, hweights]
  apply Finset.sum_congr rfl
  intro j _
  rw [hrow, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hy : y ∈ range (latticeSite (p j i) (dualMatrix (T j))) <;>
    simp [term, center, scalar, matrix, modulate, hy, zsmul_eq_mul, mul_assoc]

end

section
open Set Filter Metric FourierTransform
open scoped Topology FourierTransform NNReal ENNReal Classical

private def spectralBoxTest {d : ℕ} {B : Set (Space d)} (b : B → ℂ) (t : Space d)
    (U : Matrix (Fin d) (Fin d) ℝ) (φ : SchwartzMap (Space d) ℂ) (N : ℕ) : ℂ :=
  ∑ q : Fin d → Fin (N+1), boxCoefficient t U q * ∑' y : B, b y * φ (y.val + boxFrequency U q)

private theorem spectralBoxTest_bound {d k : ℕ} {B : Set (Space d)} (b : B → ℂ)
    (t : Space d) (U : Matrix (Fin d) (Fin d) ℝ) (p : Fin k → Space d)
    (T : Fin k → Matrix (Fin d) (Fin d) ℝ) (hcover : ∀ y ∈ B, ∃ j, y - p j ∈ matrixLattice (T j))
    (M : ℝ≥0) (hM : ∀ c : Space d, (∑' y : {y : B // dist y.val c ≤ 1}, ‖b y.val‖ₑ) ≤ M)
    (x : Space d) (n N : ℕ) :
    let Q := Finset.univ.biUnion fun j => boxHits (dualMatrix U) (matrixLattice (T j)) (p j) x (atomRadius n) N
    ‖spectralBoxTest b t U (atomTest n x) N‖ ≤ Q.card * (M : ℝ) / ((N : ℝ) + 1)^d := by
  intro Q
  let w (q : Fin d → Fin (N+1)) := ∑' y : B, b y * atomTest n x (y.val + boxFrequency U q)
  have hzero (q) (hq : q ∉ Q) : w q = 0 := by
    have hz' (y : B) : b y * atomTest n x (y.val + boxFrequency U q) = 0 := by
      by_cases hz : atomTest n x (y.val + boxFrequency U q) = 0
      · simp [hz]
      obtain ⟨j, hj⟩ := hcover _ y.property
      apply False.elim (hq (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.val, hj, dist_lt_atomRadius_of_ne hz⟩⟩))
    simp [w, hz']
  have hw (q) : ‖w q‖ ≤ M := translated_sum_ball_bound b 1 M hM (atomTest n x) x (norm_atomTest_le n x)
    (fun _ hy => (dist_lt_atomRadius_of_ne hy).le.trans (pow_le_one₀ (by norm_num) (by norm_num))) _
  have hnorm (q : Fin d → Fin (N+1)) : ‖boxCoefficient t U q‖ = (((N : ℝ) + 1)^d)⁻¹ := by
    have hN : ‖(N : ℂ) + 1‖ = (N : ℝ) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (N+1)
    simp [boxCoefficient, boxWeight, hN]
  change ‖∑ q, boxCoefficient t U q * w q‖ ≤ _
  rw [← Finset.sum_subset (Finset.subset_univ Q) (fun q _ hq => by rw [hzero q hq, mul_zero])]
  calc
    _ ≤ ∑ _q ∈ Q, (((N : ℝ) + 1)^d)⁻¹ * M :=
      norm_sum_le_of_le _ (fun q _ => by rw [norm_mul, hnorm]; gcongr; exact hw q)
    _ = _ := by simp; ring

private theorem box_ratio_tendsto (d C : ℕ) :
    Tendsto (fun N : ℕ => (((N : ℝ) + C + 1) / (N + 1))^d) atTop (𝓝 1) := by
  have h := (tendsto_add_mul_div_add_mul_atTop_nhds ((C : ℝ)+1) 1 1 (one_ne_zero : (1 : ℝ) ≠ 0)).pow d
  simpa [add_comm, add_left_comm, add_assoc] using h

private theorem atom_zero_outside_finite_orbits {d k : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BoundedRecord b)
    (t : Space d) (U : Matrix (Fin d) (Fin d) ℝ) (hU : U.det ≠ 0)
    (p : Fin k → Space d) (T : Fin k → Matrix (Fin d) (Fin d) ℝ) (hT : ∀ j, (T j).det ≠ 0)
    (hcover : ∀ y ∈ B, ∃ j, y - p j ∈ matrixLattice (T j)) (x : Space d)
    (hx : ∀ j, ((matrixLattice (T j)).mkQ '' (matrixLattice (dualMatrix U) : Set (Space d))).Finite →
      x ∉ enlargedCoset (matrixLattice (dualMatrix U)) (matrixLattice (T j)) (p j)) :
    testAtom (restrictedFourierLinear hμ hA (range (latticeSite t U))) x = 0 := by
  let L := restrictedFourierLinear hμ hA (range (latticeSite t U))
  have hL : HasLocalTestBounds L := by
    simpa [L, Set.iInter_const] using restrictedFourierLinear_hasLocalTestBounds hμ hA hν hB
      (fun _ : Unit => t) (fun _ => U) (fun _ => hU)
  obtain ⟨M, hM⟩ := joint_variation hA hB 1
  have hbound (m : ℕ) : (m : ℝ) * ‖testAtom L x‖ ≤ k * (M : ℝ) := by
    obtain ⟨C, hC⟩ := cover_box_packing (dualMatrix U) (dualMatrix_det_ne_zero U hU) T hT p x hx m
    apply le_of_tendsto ((tendsto_testAtom hL x).norm.const_mul (m : ℝ))
    filter_upwards [hC] with n hn
    let φ := atomTest n x
    have hbox : Tendsto (spectralBoxTest b t U φ) atTop (𝓝 (L φ)) :=
      spectral_box_limit_on_test hμ hA hν hB t U hU φ
    have hlim := (box_ratio_tendsto d C).const_mul ((k : ℝ) * M)
    rw [mul_one] at hlim
    apply le_of_tendsto_of_tendsto' (hbox.norm.const_mul (m : ℝ)) hlim
    intro N
    let Q := Finset.univ.biUnion fun j =>
      boxHits (dualMatrix U) (matrixLattice (T j)) (p j) x (atomRadius n) N
    have hcount : (m : ℝ) * Q.card ≤ k * (((N : ℝ) + C + 1)^d) := by exact_mod_cast hn N
    have htest := spectralBoxTest_bound b t U p T hcover M (fun c => (hM c).2) x n N
    change (m : ℝ) * ‖spectralBoxTest b t U φ N‖ ≤ _
    calc
      _ ≤ m * (Q.card * (M : ℝ) / ((N : ℝ)+1)^d) := mul_le_mul_of_nonneg_left htest (by positivity)
      _ = (m * Q.card : ℝ) * M / ((N : ℝ)+1)^d := by ring
      _ ≤ (k * (((N : ℝ)+C+1)^d)) * M / ((N : ℝ)+1)^d := by gcongr
      _ = _ := by rw [div_pow]; ring
  by_contra hne
  have hpos : 0 < ‖testAtom L x‖ := norm_pos_iff.mpr hne
  obtain ⟨m, hm⟩ := exists_nat_gt ((k * (M : ℝ)) / ‖testAtom L x‖)
  exact ((div_lt_iff₀ hpos).mp hm).not_ge (hbound m)

/-- A spectral lattice cover forces the nonzero Fourier coefficients of each
full-rank restricted physical record onto finitely many dual-lattice cosets. -/
theorem finite_dual_classes_of_spectral_cover {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BoundedRecord b)
    (hcover : HasFiniteLatticeCover B) (t : Space d) (U : Matrix (Fin d) (Fin d) ℝ) (hU : U.det ≠ 0) :
    ((matrixLattice (dualMatrix U)).mkQ '' Function.support
      (testAtom (restrictedFourierLinear hμ hA (range (latticeSite t U))))).Finite := by
  obtain ⟨k, _, p, T, hT, hcov⟩ := hcover
  let H := matrixLattice (dualMatrix U)
  let good := {j : Fin k // ((matrixLattice (T j)).mkQ '' (H : Set (Space d))).Finite}
  let D (j : good) := enlargedCoset H (matrixLattice (T j.val)) (p j.val)
  have hfin (j : good) : (H.mkQ '' D j).Finite :=
    (finite_lattice_orbit _ _ (dualMatrix_det_ne_zero U hU) (hT j.val) (p j.val) j.property).2
  have hcov' (y) (hy : y ∈ B) : ∃ j, y - p j ∈ matrixLattice (T j) := by
    obtain ⟨j, z, hz⟩ := hcov y hy
    exact ⟨j, (mem_latticeCoset_iff ..).mp ⟨z, hz.symm⟩⟩
  apply (Set.finite_iUnion hfin).subset
  rintro _ ⟨x, hx, rfl⟩
  by_contra hout
  apply hx
  apply atom_zero_outside_finite_orbits hμ hA hν hB t U hU p T hT hcov' x
  intro j hj hg
  exact hout (mem_iUnion.mpr ⟨⟨j,hj⟩, x, hg, rfl⟩)

/-- Given a finite lattice cover on each side, the weights in the spectral
record determine a finite sum of translated, modulated full-rank combs. -/
theorem spectral_comb_of_lattice_covers {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BoundedRecord b)
    (hcovA : HasFiniteLatticeCover A) (hcovB : HasFiniteLatticeCover B) :
    IsFiniteModulatedLatticeCombSum (𝓕 μ) :=
  spectral_comb_of_finite_dual_classes hμ hA hν hB hcovA
    (finite_dual_classes_of_spectral_cover hμ hA hν hB hcovB)

end

end HalfBall.Weights
