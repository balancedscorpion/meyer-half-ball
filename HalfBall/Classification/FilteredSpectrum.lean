module
public import HalfBall.Classification.NoHoles
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall
open MeyerGeneralProblem.LevOlevskii
open Set Metric FourierTransform Filter
open scoped FourierTransform Topology
variable {p : ℕ} {ι : Type*} [Fintype ι]

/-- The possible spectral sites of a finite sum of modulations. -/
def shiftedSites (E : Set (V p)) (u : ι → V p) := {z | ∃ i, z-u i ∈ E}

theorem shiftedSites_cap {E : Set (V p)} {M : ℕ} (h : BallCap E M) (u : ι → V p) :
    BallCap (shiftedSites E u) (Fintype.card ι * M) := by
  classical
  intro x T hT
  let F (i : ι) := T.filter (fun z => z-u i ∈ E)
  have hF (i : ι) : (F i).card ≤ M := by
    let e : V p ↪ V p := ⟨fun z => z-u i, sub_left_injective⟩
    have hh := h (x-u i) ((F i).map e) (by
      intro z hz
      obtain ⟨t,ht,rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨htT,htE⟩ := Finset.mem_filter.mp ht
      exact ⟨htE,by simpa [e,mem_ball] using (hT htT).2⟩)
    simpa using hh
  have hsub : T ⊆ Finset.univ.biUnion F := by
    intro z hz
    obtain ⟨i,hi⟩ := (hT hz).1
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hz,hi⟩⟩
  calc T.card ≤ _ := Finset.card_le_card hsub
       _ ≤ ∑ i, (F i).card := Finset.card_biUnion_le
       _ ≤ ∑ _ : ι, M := Finset.sum_le_sum fun i _ => hF i
       _ = _ := by simp

def shiftedSpectrum (ν : TemperedDistribution (V p) ℂ) (u : ι → V p) (c : ι → ℂ) :
    TemperedDistribution (V p) ℂ :=
  ∑ i, c i • (ν.comp (SchwartzMap.compSubConstCLM ℂ (-u i)))

theorem shiftedSpectrum_apply (ν : TemperedDistribution (V p) ℂ) (u : ι → V p) (c : ι → ℂ)
    (φ : SchwartzMap (V p) ℂ) :
    shiftedSpectrum ν u c φ = ∑ i, c i * ν ((SchwartzMap.compSubConstCLM ℂ (-u i)) φ) := by
  let ev : TemperedDistribution (V p) ℂ →L[ℂ] ℂ := PointwiseConvergenceCLM.evalCLM _ _ φ
  let v (i : ι) : TemperedDistribution (V p) ℂ := ν.comp (SchwartzMap.compSubConstCLM ℂ (-u i))
  change ev (∑ i, c i • v i) = _
  simp only [map_sum,map_smul]
  rfl

/-- Spectral expansions only use compact tests. Coincident shifted
frequencies add their weights, including complete cancellation. -/
theorem shiftedSpectrum_atoms {ν : TemperedDistribution (V p) ℂ} {B : Set (V p)}
    {b : B → ℂ} (hb : HasLocallyAtomicExpansion ν B b) (u : ι → V p) (c : ι → ℂ)
    (φ : SchwartzMap (V p) ℂ) (hc : HasCompactSupport φ) :
    HasSum (fun z : shiftedSites B u => (∑ i, c i * recordWeight b (z.val-u i)) * φ z)
      (shiftedSpectrum ν u c φ) := by
  classical
  let g (i : ι) (z : shiftedSites B u) := recordWeight b (z.val-u i) * φ z
  have hs (i : ι) : HasSum (g i) (ν ((SchwartzMap.compSubConstCLM ℂ (-u i)) φ)) := by
    let e (x : B) : shiftedSites B u := ⟨x.val+u i,⟨i,by simpa only [add_sub_cancel_right] using x.property⟩⟩
    have hinj : Function.Injective e := fun x y h => Subtype.ext (add_right_cancel (congrArg Subtype.val h))
    apply (hinj.hasSum_iff (fun z hz => ?_)).mp
    · simpa [g,e,Function.comp_def,recordWeight,SchwartzMap.compSubConstCLM_apply] using
        hb.2 ((SchwartzMap.compSubConstCLM ℂ (-u i)) φ) (hc.comp_homeomorph (Homeomorph.subRight (-u i)))
    · have hout : z.val-u i ∉ B := fun h => hz ⟨⟨_,h⟩,Subtype.ext (sub_add_cancel ..)⟩
      simp [g,recordWeight,hout]
  rw [shiftedSpectrum_apply]
  simpa [g,Finset.sum_mul,mul_assoc] using hasSum_sum (s := Finset.univ)
    (fun i _ => (hs i).mul_left (c i))

def characterSum (u : ι → V p) (c : ι → ℂ) (x : V p) := ∑ i, c i * (frequencyPhase (u i) x : ℂ)

/-- Double Fourier transformation of the filtered spectrum on a compact
test multiplies the physical atoms by the character sum and reflects
their locations. -/
theorem shiftedSpectrum_transform {μ : TemperedDistribution (V p) ℂ} {A : Set (V p)}
    {a : A → ℂ} (ha : HasLocallyAtomicExpansion μ A a) (u : ι → V p) (c : ι → ℂ)
    (φ : SchwartzMap (V p) ℂ) (hc : HasCompactSupport φ) :
    HasSum (fun z : A => (a z * characterSum u c z) * φ (-z.val))
      ((𝓕 (shiftedSpectrum (𝓕 μ) u c)) φ) := by
  let f i := 𝓕 ((SchwartzMap.compSubConstCLM ℂ (-u i)) (𝓕 φ))
  have hval (i) (x : V p) : f i x = (frequencyPhase (u i) x : ℂ) * φ (-x) := by
    rw [show f i x = _ from fourier_test_add (𝓕 φ) (u i) x]
    have hh := congrArg (fun g : SchwartzMap (V p) ℂ => g (-x)) (fourierInv_fourier_eq (F := SchwartzMap (V p) ℂ) φ)
    change (𝓕 (𝓕 φ)) (- -x) = φ (-x) at hh
    rw [← hh, neg_neg]
  have hcomp (i) : HasCompactSupport (f i : V p → ℂ) := by
    rw [show (f i : V p → ℂ) = fun x => (frequencyPhase (u i) x : ℂ) * (φ ∘ Homeomorph.neg (V p)) x from funext (hval i)]
    exact (hc.comp_homeomorph _).mul_left
  have hs := hasSum_sum (s := Finset.univ) (fun i _ => (ha.2 _ (hcomp i)).mul_left (c i))
  simpa only [TemperedDistribution.fourier_apply,shiftedSpectrum_apply,characterSum,Finset.sum_mul,
    Finset.mul_sum,hval,f,mul_assoc,mul_comm,mul_left_comm] using hs

end HalfBall
