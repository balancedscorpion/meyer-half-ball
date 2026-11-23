module

public import HalfBall.Fourier.Localization
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Fourier

open Filter MeasureTheory Set FourierTransform
open scoped Topology InnerProductSpace FourierTransform ContDiff

variable {p : ℕ}

/-- A single normalized window for the direction η. Its physical support is
strictly inside the measured unit half-ball. -/
theorem exists_window {η : V p} (hη : ‖η‖ = 1) :
    ∃ h : SchwartzMap (V p) ℂ, h 0 = 1 ∧ Function.support (𝓕 h : SchwartzMap (V p) ℂ) ⊆ halfBall η 1 := by
  let c := (1/2:ℝ) • η
  let b : ContDiffBump c := ⟨1/8,1/4,by norm_num,by norm_num⟩
  let f : V p → ℂ := Complex.ofRealCLM ∘ b.normed volume
  have hc : HasCompactSupport f := b.hasCompactSupport_normed.comp_left rfl
  let θ := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff_normed)
  refine ⟨𝓕⁻ θ,?_,?_⟩
  · rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq]
    simp only [inner_zero_right,AddChar.map_zero_eq_one,one_smul]
    change ∫ x, ((b.normed volume x : ℝ):ℂ) = 1
    simpa only [← integral_complex_ofReal,Complex.ofReal_one] using congrArg ((↑) : ℝ → ℂ) (b.integral_normed (μ := volume))
  · rw [fourier_fourierInv_eq]
    intro x hx
    have hn : b.normed volume x ≠ 0 := by
      intro hz; apply hx; change ((b.normed volume x : ℝ):ℂ) = 0; simp [hz]
    have hm : x ∈ Function.support (b.normed volume) := hn
    rw [b.support_normed_eq] at hm
    have hd : ‖x-c‖ < 1/4 := hm
    have hcn : ‖c‖ = 1/2 := by norm_num [c,norm_smul,hη]
    have hinner : ⟪η,c⟫_ℝ = 1/2 := by simp [c,real_inner_smul_right,hη]
    constructor
    · change 0 ≤ ⟪η,x⟫_ℝ
      have hcs := abs_real_inner_le_norm η (x-c)
      rw [hη,one_mul,inner_sub_right,hinner] at hcs
      linarith [(abs_le.mp hcs).1]
    · rw [Metric.mem_closedBall,dist_zero_right]
      linarith [norm_le_norm_add_norm_sub c x,norm_sub_rev x c]

/-- The normalized window sees, up to an arbitrary inverse power of R, a
finite atomic record on a bounded frequency region. At every genuine site
in that region the corresponding coefficient is nonzero. -/
theorem compact_atomic_model {T : TemperedDistribution (V p) ℂ} {B : Set (V p)}
    (hB : LocallyFiniteSites B) (hT : LocalAtoms T B) (h : SchwartzMap (V p) ℂ)
    {Q : ℝ} (hQ : 0 ≤ Q) (N : ℕ) :
    ∃ (U : Finset (V p)) (w : V p → ℂ) (C : ℝ), 0 ≤ C ∧ (↑U : Set (V p)) ⊆ B ∧
      (∀ s ∈ B, ‖s‖ ≤ Q → s ∈ U ∧ w s ≠ 0) ∧
      ∀ {R : ℝ} (hR : 1 ≤ R) (q : V p), ‖q‖ ≤ Q →
        R^N * ‖T (sample h R (by linarith) q) - ∑ u ∈ U, w u * h (R • (u-q))‖ ≤ C := by
  classical
  obtain ⟨a,ha,hatom⟩ := hT
  let b : ContDiffBump (0 : V p) := ⟨Q+1,Q+2,by linarith,by linarith⟩
  obtain ⟨C,hC,herr⟩ := remainder_action T h hQ b (by rfl) N
  let U := (hB _ (isCompact_closedBall 0 (Q+2))).toFinset
  let w (u : V p) := if hu : u ∈ B then a ⟨u,hu⟩ * (b u : ℂ) else 0
  refine ⟨U,w,C,hC,(fun _ hs => ((Set.Finite.mem_toFinset _).mp hs).1),?_,?_⟩
  · intro s hs hnorm
    have h1 : b s = 1 := b.one_of_mem_closedBall (by simpa [b] using (by linarith : ‖s‖ ≤ Q+1))
    refine ⟨(Set.Finite.mem_toFinset _).mpr ⟨hs,by simpa using (by linarith : ‖s‖ ≤ Q+2)⟩,?_⟩
    simpa [w,hs,h1] using ha ⟨s,hs⟩
  · intro R hR q hq
    let ψ := sample h R (by linarith : 0 < R) q
    let P : Finset B := U.preimage Subtype.val Subtype.val_injective.injOn
    have hP (u : B) : u ∈ P ↔ ‖u.val‖ ≤ Q+2 := by
      simp [P,U,Metric.mem_closedBall]
    have hfinite := hatom (cut b ψ) (b.hasCompactSupport.smul_right (f' := (ψ : V p → ℂ)))
    have hsum := hfinite.unique (hasSum_sum_of_ne_finset_zero (s := P) (fun u hu => by
      have hout : b.rOut ≤ dist u.val 0 := by simpa [b] using (not_le.mp (fun h' => hu ((hP _).mpr h'))).le
      change a u * ((b u.val) • ψ u.val) = 0
      simp [b.zero_of_le_dist hout]))
    have heq : T (cut b ψ) = ∑ z ∈ U, w z * h (R • (z-q)) := by
      rw [hsum]
      have hi : P.image Subtype.val = U := by
        ext z; constructor
        · rintro hz
          obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
          exact (Set.Finite.mem_toFinset _).mpr ⟨u.property,by simpa using (hP u).mp hu⟩
        · intro hz
          have hh := (Set.Finite.mem_toFinset _).mp hz
          exact Finset.mem_image.mpr ⟨⟨z,hh.1⟩,(hP _).mpr (by simpa using hh.2),rfl⟩
      rw [← hi,Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
      apply Finset.sum_congr rfl
      intro u _
      change a u * (b u.val • h (R • (u.val-q))) = _
      simp [w,u.property,Complex.real_smul,mul_assoc]
    rw [← heq]; exact herr hR q hq

end HalfBall.Fourier
