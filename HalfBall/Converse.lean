module

public import HalfBall.FourierCarriers
public import HalfBall.Poisson.Comb
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall

open MeasureTheory FourierTransform Filter Set
open scoped InnerProductSpace FourierTransform

/-- A finite sum of weighted, translated and modulated lattice combs, as
an equality of distributions on all Schwartz tests. The lattice basis,
shift, frequency and complex coefficient may differ for every summand. -/
def WeightedLatticeCombs {p : ℕ} (μ : TemperedDistribution (V p) ℂ) : Prop :=
  ∃ (m : ℕ) (L : Fin m → LatticeCoset p) (v : Fin m → V p) (c : Fin m → ℂ),
    ∀ φ : SchwartzMap (V p) ℂ, μ φ =
      ∑ i, c i * ∑' n, Poisson.phase ⟪v i,(L i).site n⟫_ℝ * φ ((L i).site n)

/-- Compact tests vanishing on a locally finite set U detect any genuine atom
outside U. Its distance from other sites may depend on the chosen atom. -/
theorem localAtoms_subset_of_vanishing {p} {μ : TemperedDistribution (V p) ℂ}
    {A U : Set (V p)} (hA : LocallyFiniteSites A) (hU : LocallyFiniteSites U)
    (hμ : LocalAtoms μ A)
    (h : ∀ φ : SchwartzMap (V p) ℂ, HasCompactSupport φ → (∀ u ∈ U, φ u = 0) → μ φ = 0) :
    A ⊆ U := by
  classical
  obtain ⟨a,ha,hμ⟩ := hμ
  intro x hx
  by_contra hxu
  have hfinite : LocallyFiniteSites (A ∪ U) := by
    intro K hK
    rw [union_inter_distrib_right]
    exact (hA _ hK).union (hU _ hK)
  obtain ⟨d,hd,_,hsep⟩ := anchor_isolation hfinite x
  let b : ContDiffBump x := ⟨d/2,d,by positivity,by linarith⟩
  let f : V p → ℂ := Complex.ofRealCLM ∘ b
  have hc : HasCompactSupport f := b.hasCompactSupport.comp_left rfl
  let φ := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hxφ : φ x = 1 := by
    change ((b x : ℝ):ℂ) = 1
    rw [b.one_of_mem_closedBall (by simpa using b.rIn_pos.le)]; norm_num
  have hz {s} (hs : s ∈ A ∪ U) (hne : s ≠ x) : φ s = 0 := by
    change ((b s : ℝ):ℂ) = 0
    rw [b.zero_of_le_dist (by simpa [b,dist_eq_norm] using hsep s hs hne)]
    norm_num
  let i : A := ⟨x,hx⟩
  have hsingle := (hμ φ hc).unique (hasSum_single i (fun j hj => by
    rw [hz (Or.inl j.property) (fun he => hj (Subtype.ext he)),mul_zero]))
  have hv := h φ hc (fun u hu => hz (Or.inr hu) (fun he => hxu (he ▸ hu)))
  apply ha i
  simpa [hv, i, hxφ] using hsingle.symm

/-- The two actual carriers of a finite comb sum lie in finite unions of the
physical cosets and the modulated reciprocal cosets, respectively. This
allows overlapping cosets and cancellation at individual sites. -/
theorem lattice_covers_of_weighted_combs {p} {μ : TemperedDistribution (V p) ℂ}
    {A B : Set (V p)} (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B)
    (hμ : LocalAtoms μ A) (hν : LocalAtoms (𝓕 μ) B) (hcomb : WeightedLatticeCombs μ) :
    LatticeCovered A ∧ LatticeCovered B := by
  obtain ⟨m,L,v,c,h⟩ := hcomb
  let U (D : Fin m → LatticeCoset p) := ⋃ i, range (D i).site
  have hU (D : Fin m → LatticeCoset p) : LocallyFiniteSites (U D) :=
    locallyFinite_of_lattice_cover ⟨m,D,Subset.rfl⟩
  constructor
  · refine ⟨m,L,localAtoms_subset_of_vanishing hA (hU L) hμ (fun φ _ hz => ?_)⟩
    rw [h]
    apply Finset.sum_eq_zero
    intro i _
    have hzero (n) : φ ((L i).site n) = 0 := hz _ (mem_iUnion.mpr ⟨i,mem_range_self _⟩)
    simp [hzero]
  · let D i := Poisson.reciprocal (L i) (v i)
    refine ⟨m,D,localAtoms_subset_of_vanishing hB (hU D) hν (fun φ hc hz => ?_)⟩
    rw [TemperedDistribution.fourier_apply,h]
    apply Finset.sum_eq_zero
    intro i _
    have hzero (n) : φ ((D i).site n) = 0 := hz _ (mem_iUnion.mpr ⟨i,mem_range_self _⟩)
    have hP := Poisson.comb_poisson (L i) (v i) φ hc
    change _ = _ * ∑' n, _ * φ ((D i).site n) at hP
    simp only [hzero,mul_zero,tsum_zero] at hP
    exact mul_eq_zero_of_right _ ((mul_eq_zero.mp hP).resolve_left
      (by exact_mod_cast (Poisson.jacobian_pos (L i)).ne'))

/-- The converse of Theorem 1.1, in a form stronger than existential
half-ball witnesses. Both directions and both positive divergent sequences
are arbitrary and independent. -/
theorem half_ball_converse {p} {μ : TemperedDistribution (V p) ℂ} {A B : Set (V p)}
    (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B)
    (hμ : LocalAtoms μ A) (hν : LocalAtoms (𝓕 μ) B) (hcomb : WeightedLatticeCombs μ)
    (ω η : V p) (R S : ℕ → ℝ) (hRpos : ∀ j, 0 < R j) (hR : Tendsto R atTop atTop)
    (hSpos : ∀ j, 0 < S j) (hS : Tendsto S atTop atTop) :
    HalfBallCount A ω R ∧ HalfBallCount B η S := by
  obtain ⟨hAc,hBc⟩ := lattice_covers_of_weighted_combs hA hB hμ hν hcomb
  exact ⟨halfBallCount_of_lattice_cover hAc ω hRpos hR,
    halfBallCount_of_lattice_cover hBc η hSpos hS⟩

/-- The independent half-ball density witnesses in Theorem 1.1. -/
def IndependentHalfBallData {p} (A B : Set (V p)) : Prop :=
  ∃ (ω η : V p) (R S : ℕ → ℝ), ‖ω‖ = 1 ∧ ‖η‖ = 1 ∧ HalfBallCount A ω R ∧ HalfBallCount B η S

theorem independentHalfBallData_of_weighted_combs {p} (hp : 0 < p)
    {μ : TemperedDistribution (V p) ℂ} {A B : Set (V p)}
    (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B) (hμ : LocalAtoms μ A)
    (hν : LocalAtoms (𝓕 μ) B) (hcomb : WeightedLatticeCombs μ) : IndependentHalfBallData A B := by
  let u : V p := PiLp.single 2 (⟨0,hp⟩ : Fin p) (1:ℝ)
  have hu : ‖u‖ = 1 := by simp [u]
  let R (j : ℕ) := ((j+1 : ℕ):ℝ)
  have hpos (j : ℕ) : 0 < R j := by dsimp [R]; positivity
  have hlim : Tendsto R atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  exact ⟨u,u,R,R,hu,hu,half_ball_converse hA hB hμ hν hcomb u u R R hpos hlim hpos hlim⟩

end HalfBall
