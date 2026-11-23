module

public import HalfBall.Classification.SeparatedClasses
public import HalfBall.FourierCarriers
public import AppendixA.SpectralWindow
public import AppendixA.CompactApproximation
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall

open Set Metric Filter FourierTransform MeasureTheory
open scoped FourierTransform Topology Convolution
open MeyerGeneralProblem.LevOlevskii

private theorem combine_windows {p} {r s : ℝ} (φ ψ : SchwartzMap (V p) ℂ)
    (hφ : Function.support φ ⊆ closedBall 0 r) (hψ : Function.support ψ ⊆ closedBall 0 s) :
    ∃ f : SchwartzMap (V p) ℂ, Function.support f ⊆ closedBall 0 (r+s) ∧
      ∀ z, (𝓕 f) z = (𝓕 φ) z * (𝓕 ψ) z := by
  let M := ContinuousLinearMap.mul ℂ ℂ
  let f := SchwartzMap.convolution M φ ψ
  refine ⟨f,?_,fun z => ?_⟩
  · intro y hy
    have hm : y ∈ Function.support ((φ : V p → ℂ) ⋆[M] (ψ : V p → ℂ)) := by
      simpa only [f, SchwartzMap.convolution_apply,Function.mem_support] using hy
    obtain ⟨v,hv,w,hw,rfl⟩ := support_convolution_subset M hm
    simpa only [mem_closedBall,dist_zero_right] using
      (norm_add_le v w).trans (add_le_add (show ‖v‖ ≤ r by simpa using hφ hv)
        (show ‖w‖ ≤ s by simpa using hψ hw))
  · unfold f
    rw [SchwartzMap.fourier_convolution]
    rfl

/-- A single spectral window, chosen before the carrier and the point,
contains a smooth test whose Fourier transform picks out that point. -/
theorem isolated_window_of_ballCap (p M : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ E : Set (V p), BallCap E M → ∀ x : V p,
      ∃ φ : SchwartzMap (V p) ℂ, Function.support φ ⊆ closedBall 0 R ∧
        (𝓕 φ) x = 1 ∧ ∀ y ∈ E, y ≠ x → (𝓕 φ) y = 0 := by
  obtain ⟨r,hr,hiso⟩ := bandlimited_isolation_at_point p (η := 1) zero_lt_one
  refine ⟨(M+1)*r,by positivity,fun E hE x => ?_⟩
  obtain ⟨F,rfl,hF⟩ := separated_classes_of_ballCap hE
  have aux (n : ℕ) (G : Fin n → Set (V p))
      (hG : ∀ i, (G i).Pairwise (fun a b => 1 ≤ dist a b)) :
      ∃ φ : SchwartzMap (V p) ℂ, Function.support φ ⊆ closedBall 0 (((n:ℝ)+1)*r) ∧
        (𝓕 φ) x = 1 ∧ ∀ i y, y ∈ G i → y ≠ x → (𝓕 φ) y = 0 := by
    induction n with
    | zero =>
      obtain ⟨φ,hφ,hx,_⟩ := hiso ∅ (by simp) x
      exact ⟨φ,by simpa using hφ,hx,fun i => i.elim0⟩
    | succ n ih =>
      obtain ⟨φ,hφ,hx,hz⟩ := ih (fun i => G i.succ) (fun i => hG i.succ)
      obtain ⟨ψ,hψ,hψx,hψz⟩ := hiso (G 0) (hG 0) x
      obtain ⟨f,hf,hprod⟩ := combine_windows φ ψ hφ hψ
      refine ⟨f,?_,by simp [hprod,hx,hψx],?_⟩
      · convert hf using 2
        push_cast
        ring
      · refine Fin.cases (fun y hy hn => ?_) (fun i y hy hn => ?_)
        · simp [hprod,hψz y hy hn]
        · simp [hprod,hz i y hy hn]
  obtain ⟨φ,hs,hx,hz⟩ := aux M F hF
  exact ⟨φ,hs,hx,fun y hy hn => by obtain ⟨i,hi⟩ := mem_iUnion.mp hy; exact hz i y hi hn⟩

/-- A compact-test expansion evaluates a Schwartz test which isolates a
single site, even when the absolute weights grow too fast to give a
global unordered expansion on all tests. -/
theorem evaluate_isolated_site {p} {E : Set (V p)} {T : TemperedDistribution (V p) ℂ}
    {a : E → ℂ} (hT : ∀ φ : SchwartzMap (V p) ℂ, HasCompactSupport φ →
      HasSum (fun z : E => a z * φ z) (T φ)) (x : E) (f : SchwartzMap (V p) ℂ)
    (hz : ∀ z : E, z ≠ x → f z = 0) : T f = a x * f x := by
  obtain ⟨ψ,hc,hbound,hevent,hlim⟩ := exists_bounded_compact_schwartz_approximation f
  have he : ∀ᶠ n in atTop, T (ψ n) = a x * f x := by
    filter_upwards [hevent x] with n hn
    have hzero (z : E) (hne : z ≠ x) : ψ n z = 0 := by
      apply norm_le_zero_iff.mp
      simpa [hz z hne] using hbound n z
    have hv := (hT (ψ n) (hc n)).unique (hasSum_single x (fun z hne => by simp [hzero z hne]))
    simpa [hn] using hv
  exact tendsto_nhds_unique (T.continuous.continuousAt.tendsto.comp hlim) (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm))

/-- Qualitative detection in Lemma B.1. The same bounded test window
determines vanishing for every distribution with the prescribed site cap.
The local atomic coefficients may vanish, as happens after multiplication
by a trigonometric polynomial. -/
theorem spectral_window_uniqueness (p M : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ (T : TemperedDistribution (V p) ℂ) (E : Set (V p))
      (a : E → ℂ), BallCap E M →
      (∀ φ : SchwartzMap (V p) ℂ, HasCompactSupport φ → HasSum (fun z : E => a z * φ z) (T φ)) →
      (∀ φ : SchwartzMap (V p) ℂ, Function.support φ ⊆ closedBall 0 R → (𝓕 T) φ = 0) →
      T = 0 := by
  obtain ⟨R,hR,hiso⟩ := isolated_window_of_ballCap p M
  refine ⟨R,hR,fun T E a hE hT hw => ?_⟩
  have hz (z : E) : a z = 0 := by
    obtain ⟨φ,hs,hφ,hz⟩ := hiso E hE z
    have hv := evaluate_isolated_site hT z (𝓕 φ) (fun i hi => hz i i.property (fun h => hi (Subtype.ext h)))
    simpa [hφ,show T (𝓕 φ) = 0 from hw φ hs] using hv.symm
  ext1 f
  obtain ⟨ψ,hc,_,_,hlim⟩ := exists_bounded_compact_schwartz_approximation f
  have hzero (n : ℕ) : T (ψ n) = 0 := by
    simpa [hz] using (hT (ψ n) (hc n)).tsum_eq.symm
  exact tendsto_nhds_unique (T.continuous.continuousAt.tendsto.comp hlim)
    (tendsto_const_nhds.congr (fun n => (hzero n).symm))

end HalfBall
