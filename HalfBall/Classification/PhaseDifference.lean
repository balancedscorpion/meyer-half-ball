module
public import HalfBall.Classification.IsolatingRecovery
public import HalfBall.Classification.FilteredSpectrum
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall.Classification
open Set Filter Metric FourierTransform Finset
open scoped FourierTransform Topology InnerProductSpace
open MeyerGeneralProblem.LevOlevskii

variable {p : ℕ}

private theorem agree_on_sites {T : TemperedDistribution (V p) ℂ} {A : Set (V p)}
    (h : LocalAtoms T A) (f g : SchwartzMap (V p) ℂ) (he : ∀ x ∈ A, f x = g x) : T f = T g := by
  obtain ⟨a,_,h⟩ := h
  obtain ⟨ψ,hc,hbound,_,hlim⟩ := exists_bounded_compact_schwartz_approximation (f-g)
  have hz (n : ℕ) (x : A) : ψ n x = 0 := norm_le_zero_iff.mp (by
    simpa [he x x.property] using hbound n x)
  have hh (n) : T (ψ n) = 0 := by simpa [hz] using (h _ (hc n)).tsum_eq.symm
  have := tendsto_nhds_unique (T.continuous.continuousAt.tendsto.comp hlim)
    (tendsto_const_nhds.congr (fun n => (hh n).symm))
  exact sub_eq_zero.mp ((T.map_sub f g).symm.trans this)

def difference (μ : TemperedDistribution (V p) ℂ) (t : V p) (φ : SchwartzMap (V p) ℂ) :=
  μ (𝓕 φ) - μ ((SchwartzMap.compSubConstCLM ℂ t) (𝓕 φ))

private theorem difference_expansion {μ : TemperedDistribution (V p) ℂ} {B : Set (V p)} {b : B → ℂ}
    (hb : HasLocallyAtomicExpansion (𝓕 μ) B b) (t : V p) (φ : SchwartzMap (V p) ℂ)
    (hc : HasCompactSupport φ) :
    HasSum (fun z : B => b z * (1-(frequencyPhase z.val t : ℂ)) * φ z) (difference μ t φ) := by
  let ψ := 𝓕⁻ ((SchwartzMap.compSubConstCLM ℂ t) (𝓕 φ))
  have hv (y : V p) : ψ y = (frequencyPhase y t : ℂ) * φ y := by
    have he := fourier_test_add (𝓕 φ) (-t) (-y)
    have hφ := congrArg (fun g : SchwartzMap (V p) ℂ => g y) (fourierInv_fourier_eq (F := SchwartzMap (V p) ℂ) φ)
    change (𝓕 (𝓕 φ)) (-y) = φ y at hφ
    change (𝓕 ((SchwartzMap.compSubConstCLM ℂ t) (𝓕 φ))) (-y) = _
    have hp : frequencyPhase (-t) (-y) = frequencyPhase y t := by
      change Real.fourierChar ⟪-y,-t⟫_ℝ = Real.fourierChar ⟪t,y⟫_ℝ
      rw [inner_neg_neg,real_inner_comm]
    simpa only [neg_neg,hφ,hp] using he
  have hcψ : HasCompactSupport (ψ : V p → ℂ) := by
    rw [show (ψ : V p → ℂ) = fun y => (frequencyPhase y t : ℂ)*φ y from funext hv]
    exact hc.mul_left
  have hs := (hb.2 φ hc).sub (hb.2 ψ hcψ)
  have he (z : B) : b z * φ z - b z * ψ z = b z*(1-(frequencyPhase z.val t : ℂ))*φ z := by rw [hv]; ring
  simpa only [he,TemperedDistribution.fourier_apply,ψ,fourier_fourierInv_eq,difference] using hs

private theorem shifted_finite {A : Set (V p)} (hA : LocallyFiniteSites A) (t : V p) :
    LocallyFiniteSites (shiftedSites A (fun i : Bool => if i then -t else 0)) := by
  intro K hK
  let u (i : Bool) := if i then -t else (0 : V p)
  have hfin (i) : ((fun x : V p => x+u i) '' (A ∩ (Homeomorph.subRight (u i) '' K))).Finite :=
    (hA _ (hK.image (Homeomorph.subRight (u i)).continuous)).image _
  apply (Set.finite_iUnion hfin).subset
  rintro z ⟨⟨i,hi⟩,hz⟩
  exact mem_iUnion.mpr ⟨i,z-u i,⟨hi,⟨z,hz,rfl⟩⟩,sub_add_cancel ..⟩

/-- Finite-window control of translated differences at each actual
spectral site. The radius is uniform over all sites; its coefficient
bound may depend on the selected site. -/
theorem phase_difference_control {μ : TemperedDistribution (V p) ℂ} {A B : Set (V p)}
    {a : A → ℂ} {b : B → ℂ} {M} (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B)
    (ha : HasLocallyAtomicExpansion μ A a) (hb : HasLocallyAtomicExpansion (𝓕 μ) B b)
    (cap : BallCap A M) :
    ∃ D : ℝ, 0 < D ∧ ∃ F : Finset B, (∀ z ∈ F, ‖z.val‖ ≤ D) ∧ ∀ x : B, ∃ C : ℝ,
      ∀ t : V p, ‖b x‖ * ‖1-(frequencyPhase x.val t : ℂ)‖ ≤
        (∑ z ∈ F, ‖b z‖ * ‖1-(frequencyPhase z.val t : ℂ)‖) * C := by
  classical
  obtain ⟨D,hD,hrec⟩ := isolating_window_recovery p (Fintype.card Bool * M)
  let S := (hB _ (isCompact_closedBall 0 D)).toFinset
  let F : Finset B := S.preimage Subtype.val Subtype.val_injective.injOn
  have hF (z : B) : z ∈ F ↔ ‖z.val‖ ≤ D := by simp [F,S,mem_closedBall]
  refine ⟨D,hD,F,fun z hz => (hF z).mp hz,fun x => ?_⟩
  obtain ⟨P,C,hP,hxP,hzP,_,hχ⟩ := hrec B hB x x.property
  refine ⟨C,fun t => ?_⟩
  let u (i : Bool) := if i then -t else (0 : V p)
  let E := shiftedSites A u
  obtain ⟨χ,hsχ,hnχ,hvχ⟩ := hχ E (shifted_finite hA t) (shiftedSites_cap cap u)
  have h₁ (y) (hy : y ∈ A) : y ∈ E := ⟨false,by simpa [u] using hy⟩
  have h₂ (y) (hy : y ∈ A) : y-t ∈ E := ⟨true,by simpa [u] using hy⟩
  have he : difference μ t χ = difference μ t P := sub_eq_sub_iff_add_eq_add.mpr (by
    rw [agree_on_sites ⟨a,ha⟩ (𝓕 χ) (𝓕 P) (fun y hy => hvχ _ (h₁ y hy)),
      agree_on_sites ⟨a,ha⟩ ((SchwartzMap.compSubConstCLM ℂ t) (𝓕 χ))
        ((SchwartzMap.compSubConstCLM ℂ t) (𝓕 P)) (fun y hy => hvχ _ (h₂ y hy))])
  have hp := (difference_expansion hb t P hP).unique
    (hasSum_single x (fun z hz => by rw [hzP z z.property (fun h => hz (Subtype.ext h)),mul_zero]))
  have hcompact : HasCompactSupport (χ : V p → ℂ) := HasCompactSupport.intro (isCompact_closedBall _ _) fun _ h => not_not.mp (mt (@hsχ _) h)
  have hsum := (difference_expansion hb t χ hcompact).unique (hasSum_sum_of_ne_finset_zero (s := F) (fun z hz => by
    have hc : χ z = 0 := by by_contra hn; exact hz ((hF _).mpr (by simpa using hsχ hn))
    rw [hc,mul_zero]))
  have heq := hp.symm.trans (he ▸ hsum)
  rw [hxP,mul_one] at heq
  calc _ = ‖∑ z ∈ F, b z * (1-(frequencyPhase z.val t : ℂ)) * χ z‖ := by rw [← norm_mul,heq]
       _ ≤ ∑ z ∈ F, ‖b z * (1-(frequencyPhase z.val t : ℂ)) * χ z‖ := norm_sum_le ..
       _ ≤ _ := by
         rw [sum_mul]; apply sum_le_sum; intro z _
         simp only [norm_mul]; exact mul_le_mul_of_nonneg_left (hnχ z) (by positivity)

end HalfBall.Classification
