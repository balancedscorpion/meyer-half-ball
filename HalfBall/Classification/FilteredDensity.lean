module
public import HalfBall.Classification.FilteredSpectrum
public import AppendixA.Covering
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall
open MeyerGeneralProblem.LevOlevskii
open Set Metric FourierTransform Filter
open scoped FourierTransform Topology
variable {p : ℕ}

/-- Finite character sums which survive at even one physical site must
survive somewhere in every sufficiently large ball. The density radius
may depend on the number of frequencies in the sum. -/
theorem dense_character_sum {ι : Type*} [Fintype ι] {μ : TemperedDistribution (V p) ℂ}
    {A B : Set (V p)} {a : A → ℂ} {b : B → ℂ} {M : ℕ}
    (hA : LocallyFiniteSites A) (ha : HasLocallyAtomicExpansion μ A a)
    (hb : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BallCap B M)
    (u : ι → V p) (c : ι → ℂ) (hp : ∃ x ∈ A, characterSum u c x ≠ 0) :
    ∃ R : ℝ, ∀ y : V p, ∃ x ∈ A, characterSum u c x ≠ 0 ∧ dist y x ≤ R := by
  classical
  let W := shiftedSpectrum (𝓕 μ) u c
  let E := shiftedSites B u
  let w (z : E) := ∑ i, c i * recordWeight b (z.val-u i)
  have hW (φ : SchwartzMap (V p) ℂ) (hc : HasCompactSupport φ) :
      HasSum (fun z : E => w z * φ z) (W φ) := shiftedSpectrum_atoms hb u c φ hc
  have hne : ∃ z : E, w z ≠ 0 := by
    by_contra! hz
    have hzero (φ : SchwartzMap (V p) ℂ) (hc : HasCompactSupport φ) : W φ = 0 := by
      simpa [hz] using (hW φ hc).tsum_eq.symm
    obtain ⟨x,hxA,hx⟩ := hp
    obtain ⟨d,hd,_,hsep⟩ := anchor_isolation hA x
    let β : ContDiffBump (-x) := ⟨d/2,d,by positivity,by linarith⟩
    let f : V p → ℂ := Complex.ofRealCLM ∘ β
    have hc : HasCompactSupport f := β.hasCompactSupport.comp_left rfl
    let φ := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)
    have hφx : φ (-x) = 1 := by
      change ((β (-x) : ℝ):ℂ) = 1
      rw [β.one_of_mem_closedBall (by simpa using β.rIn_pos.le)]; norm_num
    let i : A := ⟨x,hxA⟩
    have hφ (j : A) (hn : j ≠ i) : φ (-j.val) = 0 := by
      change ((β (-j.val) : ℝ):ℂ) = 0
      rw [β.zero_of_le_dist (by change d ≤ dist (-j.val) (-x); rw [dist_neg_neg,dist_eq_norm]; exact hsep j j.property (fun h => hn (Subtype.ext h)))]; norm_num
    have hs := (shiftedSpectrum_transform ha u c φ hc).unique (hasSum_single i (fun j hj => by simp [hφ j hj]))
    obtain ⟨ψ,hcψ,_,_,hlim⟩ := exists_bounded_compact_schwartz_approximation (𝓕 φ)
    have hv : W (𝓕 φ) = 0 := tendsto_nhds_unique (W.continuous.continuousAt.tendsto.comp hlim)
      (tendsto_const_nhds.congr (fun n => (hzero _ (hcψ n)).symm))
    change W (𝓕 φ) = (a i * characterSum u c x) * φ (-x) at hs
    exact (mul_ne_zero (ha.1 i) hx) (by simpa [hv,hφx] using hs.symm)
  obtain ⟨R,hR,hw⟩ := no_holes_in_transform p (Fintype.card ι*M)
  refine ⟨R,fun y => ?_⟩
  obtain ⟨φ,hφ,hn⟩ := hw (shiftedSites_cap hB u) hW hne (-y)
  have hc : HasCompactSupport (φ : V p → ℂ) :=
    HasCompactSupport.intro (isCompact_closedBall _ _) fun z hz => by
      by_contra h; exact hz (hφ h)
  by_contra! h
  have hz (z : A) : (a z * characterSum u c z) * φ (-z.val) = 0 := by
    by_cases hs : characterSum u c z = 0
    · simp [hs]
    · have hp : φ (-z.val) = 0 := by
        by_contra hnon
        have hd := hφ hnon
        exact (h z z.property hs).not_ge (by simpa [mem_closedBall,dist_comm] using hd)
      simp [hp]
  exact hn (by simpa only [hz,tsum_zero] using (shiftedSpectrum_transform ha u c φ hc).tsum_eq.symm)

private theorem trigPolynomial_characters (f : (Fin p → ℝ) → ℂ) (hf : f ∈ trigPolynomials p) :
    ∃ (ι : Type) (_ : Fintype ι) (u : ι → V p) (c : ι → ℂ), ∀ x, f (WithLp.ofLp x) = characterSum u c x := by
  unfold trigPolynomials at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨v,rfl⟩ := hf
    refine ⟨Unit,inferInstance,fun _ => WithLp.toLp 2 v, fun _ => 1,fun x => ?_⟩
    simp [characterSum,frequencyPhase,EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm]
  | algebraMap c =>
    exact ⟨Unit,inferInstance,fun _ => 0,fun _ => c,fun x => by simp [characterSum,frequencyPhase]⟩
  | add f g _ _ hf hg =>
    obtain ⟨I,_,u,c,hu⟩ := hf
    obtain ⟨J,_,v,b,hv⟩ := hg
    exact ⟨I ⊕ J,inferInstance,Sum.elim u v,Sum.elim c b,fun x => by
      simp [characterSum,Fintype.sum_sum_type,hu,hv]⟩
  | mul f g _ _ hf hg =>
    obtain ⟨I,_,u,c,hu⟩ := hf
    obtain ⟨J,_,v,b,hv⟩ := hg
    refine ⟨I × J,inferInstance,fun ij => u ij.1+v ij.2,fun ij => c ij.1*b ij.2,fun x => ?_⟩
    simp [characterSum,hu,hv,frequencyPhase,AddChar.map_add_eq_mul,Fintype.sum_prod_type,
      Finset.sum_mul_sum,mul_left_comm,mul_assoc]

theorem relatively_dense_filtered_atoms {μ : TemperedDistribution (V p) ℂ}
    {A B : Set (V p)} {a : A → ℂ} {b : B → ℂ} {M : ℕ}
    (hA : LocallyFiniteSites A) (ha : HasLocallyAtomicExpansion μ A a)
    (hb : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : BallCap B M)
    (f : (Fin p → ℝ) → ℂ) (hf : f ∈ trigPolynomials p) (hp : ∃ x ∈ A, f (WithLp.ofLp x) ≠ 0) :
    ∃ R : ℝ, ∀ y : V p, ∃ x ∈ A, f (WithLp.ofLp x) ≠ 0 ∧ dist y x ≤ R := by
  obtain ⟨ι,_,u,c,he⟩ := trigPolynomial_characters f hf
  simp only [he] at hp ⊢
  exact dense_character_sum hA ha hb hB u c hp

end HalfBall
