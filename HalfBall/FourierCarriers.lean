/-
The compact-test Fourier reflection argument adapts Jamie Martin’s MIT-licensed
AppendixA/FourierReflection.lean. See LICENSES/lev-olevskii-lattice-cover-MIT.txt.
-/
module

public import HalfBall.GlobalCount
public import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Set Filter FourierTransform
open scoped InnerProductSpace FourierTransform

/-- Nonzero point masses on precisely these sites, tested on compactly
supported Schwartz functions. Temperedness is distributional. -/
def LocalAtoms {p} (μ : TemperedDistribution (V p) ℂ) (A : Set (V p)) : Prop :=
  ∃ a : A → ℂ, (∀ x, a x ≠ 0) ∧ ∀ φ : SchwartzMap (V p) ℂ, HasCompactSupport φ →
    HasSum (fun x : A => a x * φ x) (μ φ)

def reflected {p} (A : Set (V p)) : Set (V p) := {x | -x ∈ A}

private def negSites {p} (A : Set (V p)) : reflected A ≃ A where
  toFun x := ⟨-x.val,x.property⟩
  invFun x := ⟨-x.val,by simp [reflected]⟩
  left_inv x := Subtype.ext (neg_neg x.val)
  right_inv x := Subtype.ext (neg_neg x.val)

/-- Reflection of the actual local atoms, valid even if their absolute
weights have no polynomial growth. -/
theorem localAtoms_double_fourier {p} {μ : TemperedDistribution (V p) ℂ} {A : Set (V p)}
    (h : LocalAtoms μ A) : LocalAtoms (𝓕 (𝓕 μ)) (reflected A) := by
  obtain ⟨a,ha,hμ⟩ := h
  refine ⟨a ∘ negSites A,fun x => ha _,fun φ hc => ?_⟩
  have hφ (x : V p) : (𝓕 (𝓕 φ)) x = φ (-x) := by
    have hi := congrArg (fun ψ : SchwartzMap (V p) ℂ => ψ (-x))
      (fourierInv_fourier_eq (F := SchwartzMap (V p) ℂ) φ)
    change (𝓕 (𝓕 φ)) (- -x) = φ (-x) at hi
    simpa only [neg_neg] using hi
  let ψ : SchwartzMap (V p) ℂ := 𝓕 (𝓕 φ)
  have hcomp : HasCompactSupport (⇑ψ) := by
    rw [show ⇑ψ = (φ : V p → ℂ) ∘ Homeomorph.neg (V p) from funext hφ]
    exact hc.comp_homeomorph _
  simpa [ψ,negSites,Function.comp_def,hφ,TemperedDistribution.fourier_apply] using
    (negSites A).hasSum_iff.mpr (hμ _ hcomp)

private theorem reflected_inter {p} (A K : Set (V p)) :
    reflected A ∩ reflected K = reflected (A ∩ K) := rfl

private theorem ncard_reflected {p} (A : Set (V p)) : (reflected A).ncard = A.ncard :=
  ncard_congr' (negSites A)

theorem locallyFinite_reflected {p} {A : Set (V p)} (h : LocallyFiniteSites A) :
    LocallyFiniteSites (reflected A) := by
  intro K hK
  have he : reflected K = (fun x : V p => -x) '' K := by ext; simp [reflected]
  have hc : IsCompact (reflected K) := he ▸ hK.image continuous_neg
  have hf := (h _ hc).image (fun x => -x)
  refine hf.subset ?_
  rintro x ⟨hx,hxK⟩
  exact ⟨-x,⟨hx,by simpa [reflected] using hxK⟩,neg_neg _⟩

theorem halfBallCount_reflected {p} {A : Set (V p)} {ω : V p} {R : ℕ → ℝ}
    (h : HalfBallCount A ω R) : HalfBallCount (reflected A) (-ω) R := by
  obtain ⟨hpos,ht,C,hC,hcount⟩ := h
  refine ⟨hpos,ht,C,hC,?_⟩
  filter_upwards [hcount] with j hj
  have he : halfBall (-ω) (R j) = reflected (halfBall ω (R j)) := by
    ext x
    simp [reflected,halfBall,halfSpace,Metric.mem_closedBall,dist_zero_right]
  rwa [he,reflected_inter,ncard_reflected]

/-- Manuscript Lemma A.1, isolated as a mathematical proposition for
tracking the missing distributional patch estimate. -/
def FourierPatchEstimate (p : ℕ) : Prop :=
  ∀ (μ : TemperedDistribution (V p) ℂ) (A B : Set (V p)) (ω : V p) (R : ℕ → ℝ),
    LocallyFiniteSites A → LocallyFiniteSites B → LocalAtoms μ A → LocalAtoms (𝓕 μ) B →
    ‖ω‖ = 1 → HalfBallCount A ω R → OrderedPatchBound B

/-- Conditional on Lemma A.1 alone, both actual carriers have uniform
local counts. The two measured directions and radius sequences are independent. -/
theorem both_carriers_of_fourier_patch_estimate {p} (hp : 0 < p) (hA1 : FourierPatchEstimate p)
    {μ : TemperedDistribution (V p) ℂ} {A B : Set (V p)} {ω η : V p} {R S : ℕ → ℝ}
    (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B)
    (hμ : LocalAtoms μ A) (hν : LocalAtoms (𝓕 μ) B)
    (hω : ‖ω‖ = 1) (hη : ‖η‖ = 1) (hR : HalfBallCount A ω R) (hS : HalfBallCount B η S) :
    ∃ M : ℕ, ∀ y : V p, (A ∩ Metric.ball y 1).ncard ≤ M ∧ (B ∩ Metric.ball y 1).ncard ≤ M := by
  have hAr := locallyFinite_reflected hA
  have hpatchB := hA1 μ A B ω R hA hB hμ hν hω hR
  have hpatchA := hA1 (𝓕 μ) B (reflected A) η S hB hAr hν (localAtoms_double_fourier hμ) hη hS
  obtain ⟨N,hN⟩ := global_local_count hp hAr (by simpa using hω : ‖-ω‖ = 1) hpatchA
    (halfBallCount_reflected hR)
  obtain ⟨M,hM⟩ := global_local_count hp hB hη hpatchB hS
  refine ⟨max N M,fun y => ⟨?_,(hM y).trans (le_max_right ..)⟩⟩
  have he : Metric.ball (-y) 1 = reflected (Metric.ball y 1) := by
    ext x
    change dist x (-y) < 1 ↔ dist (-x) y < 1
    rw [← dist_neg_neg x (-y), neg_neg]
  have hh := hN (-y)
  rw [he,reflected_inter,ncard_reflected] at hh
  exact hh.trans (le_max_left ..)

end HalfBall
