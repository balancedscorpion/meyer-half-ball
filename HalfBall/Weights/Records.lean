/-
The extension from compact tests and the variation estimates adapt AppendixA/AtomicSeries.lean
and TranslationBound.lean from the pinned lev-olevskii-lattice-cover dependency.
See LICENSES/lev-olevskii-lattice-cover-MIT.txt.
-/
module
public import HalfBall.Weights.BoundedWeights
public import HalfBall.Poisson.Samples
public import AppendixA.FiniteDualClasses
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Weights
open MeyerGeneralProblem.LevOlevskii Set Filter Metric FourierTransform
open scoped FourierTransform NNReal ENNReal Topology

structure BoundedRecord {p} {A : Set (V p)} (a : A → ℂ) : Prop where
  cover : LatticeCovered A
  bounded : ∃ C : ℝ, ∀ x, ‖a x‖ ≤ C

theorem summable_weights {p} {A : Set (V p)} {a : A → ℂ} (h : BoundedRecord a)
    (φ : SchwartzMap (V p) ℂ) : Summable (fun x : A => ‖a x * φ x‖) := by
  obtain ⟨m,L,hcov⟩ := h.cover
  choose i hi using fun x : A => mem_iUnion.mp (hcov x.property)
  choose n hn using hi
  let f (u : Fin m × (Fin p → ℤ)) := ‖φ ((L u.1).site u.2)‖
  have hf : Summable f := (summable_prod_of_nonneg (fun i => norm_nonneg _)).mpr
    ⟨fun j => summable_lattice_samples (L j) φ,(hasSum_fintype _).summable⟩
  have hinj : Function.Injective (fun x : A => (i x,n x)) := by
    intro x y he
    exact Subtype.ext ((hn x).symm.trans ((congrArg (fun u : Fin m × (Fin p → ℤ) => (L u.1).site u.2) he).trans (hn y)))
  have hs : Summable (fun x : A => ‖φ x‖) := by simpa [Function.comp_def,f,hn] using hf.comp_injective hinj
  obtain ⟨C,hC⟩ := h.bounded
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)) (hs.mul_left C)

theorem global_expansion {d} {A : Set (Space d)} {a : A → ℂ} {μ : TemperedDistribution (Space d) ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : BoundedRecord a) : HasAtomicExpansion μ A a := by
  refine ⟨hμ.1, fun φ => ?_⟩
  obtain ⟨ψ, hc, hbound, hevent, hlim⟩ := exists_bounded_compact_schwartz_approximation φ
  have hsum := summable_weights hA φ
  have hts := tendsto_tsum_of_dominated_convergence
    (f := fun (n : ℕ) (x : A) => a x * ψ n x) (g := fun x => a x * φ x) hsum
    (fun x => tendsto_const_nhds.congr' ((hevent x).mono (fun _ h => congrArg (a x * ·) h.symm)))
    (Eventually.of_forall (fun n x => by
      rw [norm_mul, norm_mul]; gcongr; exact hbound n x))
  have heq (n : ℕ) : (∑' x : A, a x * ψ n x) = μ (ψ n) := (hμ.2 _ (hc n)).tsum_eq
  have hval := tendsto_nhds_unique hts ((μ.continuous.tendsto φ).comp hlim |>.congr (fun n => (heq n).symm))
  exact hval ▸ hsum.of_norm.hasSum

theorem variation_bound {d} {A : Set (Space d)} {a : A → ℂ} (h : BoundedRecord a) (r : ℝ) :
    ∃ M : ℝ≥0, ∀ c : Space d, (∑' x : {x : A // dist x.val c ≤ r}, ‖a x.val‖ₑ) ≤ M := by
  classical
  obtain ⟨D,_,hD⟩ := lattice_cover_count h.cover
  let R := max 1 r
  let N := ⌈D*R^d⌉₊
  obtain ⟨C,hC⟩ := h.bounded
  refine ⟨(N : ℝ≥0) * Real.toNNReal C, fun c => ?_⟩
  obtain ⟨hf,hcard⟩ := hD c R (le_max_left ..)
  let X := {x : A // dist x.val c ≤ r}
  let Y := A ∩ closedBall c R
  let : Fintype Y := hf.fintype
  let e : X ↪ Y := ⟨fun x => ⟨x.val.val,x.val.property,x.property.trans (le_max_right ..)⟩,
    fun x y he => Subtype.ext (Subtype.ext (congrArg (fun v : Y => v.val) he))⟩
  let := Fintype.ofInjective e e.injective
  have hN : Fintype.card X ≤ N := (Fintype.card_le_of_embedding e).trans (by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast hcard.trans (Nat.le_ceil (D*R^d)))
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _ : X, (Real.toNNReal C : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro x _
      exact ENNReal.coe_le_coe.mpr (by exact_mod_cast (hC x.val).trans (Real.le_coe_toNNReal _))
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_right (show (Fintype.card X : ℝ≥0∞) ≤ N by exact_mod_cast hN)
        (show 0 ≤ (Real.toNNReal C : ℝ≥0∞) by positivity)

theorem joint_variation {d} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hA : BoundedRecord a) (hB : BoundedRecord b) (r : ℝ) :
    ∃ M : ℝ≥0, ∀ c : Space d,
      (∑' x : {x : A // dist x.val c ≤ r}, ‖a x.val‖ₑ) ≤ M ∧
      (∑' y : {y : B // dist y.val c ≤ r}, ‖b y.val‖ₑ) ≤ M := by
  obtain ⟨P,hP⟩ := variation_bound hA r
  obtain ⟨Q,hQ⟩ := variation_bound hB r
  exact ⟨max P Q, fun c => ⟨(hP c).trans (by exact_mod_cast le_max_left P Q),
    (hQ c).trans (by exact_mod_cast le_max_right P Q)⟩⟩

theorem atom_test_weight {d} {ν : TemperedDistribution (Space d) ℂ} {B : Set (Space d)} {b : B → ℂ}
    (hν : HasLocallyAtomicExpansion ν B b) (hB : BoundedRecord b) (x : Space d) :
    ∀ᶠ n in atTop, ν (atomTest n x) = recordWeight b x := by
  obtain ⟨η,hη,_,hsep⟩ := anchor_isolation (locallyFinite_of_lattice_cover hB.cover) x
  filter_upwards [atomRadius_tendsto.eventually_lt_const hη] with n hn
  have hzero (v : B) (hne : v.val ≠ x) : atomTest n x v.val = 0 := by
    simp [atomTest_apply,atomProfile_support n x v.val (hn.le.trans (by simpa [dist_eq_norm] using hsep _ v.property hne))]
  have hh := (global_expansion hν hB).2 (atomTest n x)
  by_cases hx : x ∈ B
  · let y : B := ⟨x,hx⟩
    have hs := hh.unique (hasSum_single y (fun v hv => by
      rw [hzero v (fun he => hv (Subtype.ext he)),mul_zero]))
    simpa [recordWeight,hx,y,atomTest_self] using hs
  · have hz (v : B) := hzero v (fun he => hx (he ▸ v.property))
    simpa [recordWeight,hx,hz] using hh.tsum_eq.symm

end HalfBall.Weights
