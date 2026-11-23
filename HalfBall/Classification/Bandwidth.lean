module

public import HalfBall.Classification.Detection
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Classification
open Set Metric FourierTransform MeasureTheory
open MeyerGeneralProblem.LevOlevskii
open scoped FourierTransform Convolution

/-- A multiplier increases the radius of compact frequency support by at
most r. It need not decay or itself be a Schwartz function. -/
def Bandwidth {p} (r : ℝ) (f : V p → ℂ) : Prop :=
  ∀ (s : ℝ) (φ : SchwartzMap (V p) ℂ), Function.support φ ⊆ closedBall 0 s →
    ∃ ψ : SchwartzMap (V p) ℂ, Function.support ψ ⊆ closedBall 0 (r+s) ∧
      ∀ x, (𝓕 ψ) x = f x * (𝓕 φ) x

variable {p : ℕ} {r s : ℝ} {f g : V p → ℂ}

theorem Bandwidth.mono (h : Bandwidth r f) (hrs : r ≤ s) : Bandwidth s f := by
  intro t φ hφ
  obtain ⟨ψ,hs,hv⟩ := h t φ hφ
  exact ⟨ψ,hs.trans (closedBall_subset_closedBall (by linarith)),hv⟩

theorem Bandwidth.const (a : ℂ) : Bandwidth 0 (fun _ : V p => a) := by
  intro t φ hφ
  refine ⟨a • φ,?_,fun x => by simp [fourier_smul]⟩
  intro x hx
  exact (zero_add t).symm ▸ hφ (fun hz => hx (by simp [hz]))

theorem Bandwidth.add (hf : Bandwidth r f) (hg : Bandwidth r g) : Bandwidth r (fun x => f x + g x) := by
  intro t φ hφ
  obtain ⟨ψ,hs,hψ⟩ := hf t φ hφ
  obtain ⟨χ,hc,hχ⟩ := hg t φ hφ
  refine ⟨ψ+χ,?_,fun x => ?_⟩
  · intro x hx
    by_contra h
    exact hx (by simp [not_not.mp (mt (@hs x) h),not_not.mp (mt (@hc x) h)])
  · change ((SchwartzMap.fourierTransformCLM ℂ) (ψ+χ)) x = _
    rw [map_add]; simp [hψ,hχ,add_mul,SchwartzMap.fourierTransformCLM_apply]

theorem Bandwidth.mul (hf : Bandwidth r f) (hg : Bandwidth s g) : Bandwidth (r+s) (fun x => f x * g x) := by
  intro t φ hφ
  obtain ⟨ψ,hs,hψ⟩ := hg t φ hφ
  obtain ⟨χ,hc,hχ⟩ := hf _ ψ hs
  exact ⟨χ,by simpa only [add_assoc] using hc,fun x => by rw [hχ,hψ,mul_assoc]⟩

theorem Bandwidth.smul (hf : Bandwidth r f) (a : ℂ) : Bandwidth r (fun x => a * f x) := by
  simpa only [zero_add] using (Bandwidth.const a).mul hf

theorem Bandwidth.sub (hf : Bandwidth r f) (hg : Bandwidth r g) : Bandwidth r (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add (hg.smul (-1))

theorem Bandwidth.sum {ι : Type*} (t : Finset ι) (F : ι → V p → ℂ) (hr : 0 ≤ r)
    (h : ∀ i ∈ t, Bandwidth r (F i)) : Bandwidth r (fun x => ∑ i ∈ t, F i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (Bandwidth.const (p := p) 0).mono hr
  | insert i t hi ih =>
    simpa only [Finset.sum_insert hi] using (h i (Finset.mem_insert_self ..)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem Bandwidth.character (u : V p) : Bandwidth ‖u‖ (fun x => (frequencyPhase u x : ℂ)) := by
  intro t φ hφ
  refine ⟨SchwartzMap.compSubConstCLM ℂ (-u) φ,?_,fourier_test_add φ u⟩
  intro x hx
  have hh : ‖x+u‖ ≤ t := by simpa using hφ (show φ (x - -u) ≠ 0 from hx)
  have ht := norm_sub_le (x+u) u
  rw [add_sub_cancel_right] at ht
  simpa [mem_closedBall] using (show ‖x‖ ≤ ‖u‖+t by linarith)

theorem Bandwidth.of_fourier (φ : SchwartzMap (V p) ℂ) (hs : Function.support φ ⊆ closedBall 0 r) :
    Bandwidth r (⇑(𝓕 φ : SchwartzMap (V p) ℂ)) := by
  intro t ψ hψ
  let L := ContinuousLinearMap.mul ℂ ℂ
  refine ⟨SchwartzMap.convolution L φ ψ,?_,fun x => by rw [SchwartzMap.fourier_convolution]; rfl⟩
  intro y hy
  have hm : y ∈ Function.support ((φ : V p → ℂ) ⋆[L] (ψ : V p → ℂ)) := by
    simpa only [SchwartzMap.convolution_apply,Function.mem_support] using hy
  obtain ⟨v,hv,w,hw,rfl⟩ := support_convolution_subset L hm
  simpa only [mem_closedBall,dist_zero_right] using (norm_add_le v w).trans
    (add_le_add (show ‖v‖ ≤ r by simpa using hs hv) (show ‖w‖ ≤ t by simpa using hψ hw))

end HalfBall.Classification
