module

public import HalfBall.Fourier.BlockRank
public import HalfBall.Fourier.SampledRows
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall

open Filter MeasureTheory Set Finset FourierTransform
open scoped FourierTransform InnerProductSpace
open HalfBall.Fourier

/-- Lemma A.1 in the finite-constant form needed by A.3. For a fixed
physical direction, choose one cutoff and sampling width before selecting an
anchor or an ordered family. Diagonal blocks resolve the anchor, lower
blocks vanish to high order, and upper blocks have uniformly bounded rows. -/
theorem fourier_patch_estimate (p : ℕ) : FourierPatchEstimate p := by
  classical
  intro μ A B η S hA hB hμ hν hη hS
  obtain ⟨h,h0,hwindow⟩ := exists_window hη
  obtain ⟨L,hL,hwidth⟩ := sampling_width h h0
  obtain ⟨hSpos,hSlim,C₀,hC₀,hcount⟩ := hS
  have hLpos : 0 < L := by linarith
  let D := (2*L)^p * unitBallVolume p
  have hD : 0 < D := mul_pos (pow_pos (by positivity) _) (unitBallVolume_pos p)
  refine ⟨C₀*D,mul_nonneg hC₀ hD.le,?_⟩
  intro s hs m E hE hdiag hlower
  have hc (i) := compact_of_patch (hE i)
  obtain ⟨U,w,C,hsw,hC,happrox⟩ := ordered_model hB hν h (p+1) hs E hc hdiag hlower
  obtain ⟨H,hH,hrows⟩ := hwidth m s U w
  obtain ⟨δ,hδ,hrank⟩ := rank_of_ordered_blocks m (w s) hsw H hH
  let V₀ i := volume.real (E i)
  let P := ∑ i, (V₀ i / D + 1)
  have hV (i) : 0 ≤ V₀ i := ENNReal.toReal_nonneg
  have hP : 0 ≤ P := sum_nonneg (fun i _ => add_nonneg (div_nonneg (hV _) hD.le) zero_le_one)
  obtain ⟨n,hn1,hnδ,hnC⟩ := ((hSlim.eventually_ge_atTop 1).and
    ((hSlim.eventually_ge_atTop (P*C/δ)).and hcount)).exists
  let R := S n
  have hR : 0 < R := hSpos n
  have hRp : 0 < R^p := pow_pos hR _
  choose Y hYE hsep hcard using fun i => sample_patch (hc i) hLpos hR
  let I := Σ i, ↥(Y i)
  have hcard' (i) : (Y i).card = ⌈V₀ i*R^p/D⌉₊ := hcard i
  have hupper : (Fintype.card I : ℝ) ≤ P*R^p := by
    change ((Fintype.card (Σ i, ↥(Y i))):ℝ) ≤ _
    rw [Fintype.card_sigma,Nat.cast_sum,Finset.sum_mul]
    apply sum_le_sum; intro i _
    simp only [Fintype.card_coe,hcard']
    have hi := Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (hV i) hRp.le) hD.le)
    have hlarge : 1 ≤ R^p := one_le_pow₀ hn1
    calc _ ≤ V₀ i*R^p/D+1 := hi.le
         _ ≤ V₀ i*R^p/D+R^p := by linarith
         _ = _ := by ring
  let e := C / R^(p+1)
  have he : 0 ≤ e := div_nonneg hC (pow_nonneg hR.le _)
  have hsmall : (Fintype.card I:ℝ)*e ≤ δ := by
    calc _ ≤ P*R^p*e := mul_le_mul_of_nonneg_right hupper he
         _ = P*C/R := by dsimp [e]; rw [pow_succ]; field_simp
         _ ≤ δ := (div_le_iff₀ hR).mpr (by
           have hh := (div_le_iff₀ hδ).mp hnδ
           simpa [R,mul_comm] using hh)
  let pos (i : I) := i.2.val
  let q (i j : I) := s+pos i-pos j
  let M : Matrix I I ℂ := fun i j => blockModel h s U w R i.1 j.1 (q i j)
  let K : Matrix I I ℂ := fun i j => (𝓕 μ) (sample h R hR (q i j))
  have hentry (i j : I) : ‖K i j-M i j‖ ≤ e := by
    apply (le_div_iff₀ (pow_pos hR (p+1))).mpr
    rw [mul_comm]
    exact happrox hn1 i.1 j.1 _ (hYE _ i.2.property) _ (hYE _ j.2.property)
  have hfull : K.rank = Fintype.card I :=
    hrank (fun i => ↥(Y i)) K M e he hsmall hentry (fun i j => hrows hR Y hsep i.1 i.2 j)
  have hphys : K.rank ≤ (A ∩ halfBall η R).ncard := sample_rank_le_half_ball hA hμ hwindow hR s pos
  have hdim : (Fintype.card I:ℝ) ≤ C₀*R^p := (Nat.cast_le.mpr (hfull ▸ hphys)).trans hnC
  have hvol : ∑ i, V₀ i ≤ C₀*D := by
    have hlower' : (∑ i, V₀ i)*R^p/D ≤ (Fintype.card I:ℝ) := by
      change _ ≤ ((Fintype.card (Σ i, ↥(Y i))):ℝ)
      rw [Fintype.card_sigma,Nat.cast_sum,Finset.sum_mul,Finset.sum_div]
      exact sum_le_sum (fun i _ => by simpa only [Fintype.card_coe,hcard'] using Nat.le_ceil (V₀ i*R^p/D))
    have hh := (div_le_iff₀ hD).mp (hlower'.trans hdim)
    apply le_of_mul_le_mul_right (a := R^p) _ hRp
    convert hh using 1
    ring
  have hfinite (i) : volume (E i) ≠ ⊤ := (hc i).measure_lt_top.ne
  calc ∑ i, volume (E i) = ∑ i, ENNReal.ofReal (V₀ i) := by
         apply sum_congr rfl; intro i _; exact (ENNReal.ofReal_toReal (hfinite i)).symm
       _ = ENNReal.ofReal (∑ i,V₀ i) := (ENNReal.ofReal_sum_of_nonneg (fun i _ => hV i)).symm
       _ ≤ _ := ENNReal.ofReal_le_ofReal hvol

/-- Independent physical and spectral half-ball counts force uniform
unit-ball counts on both actual carriers, in all of Euclidean space. -/
theorem both_carriers_relatively_separated {p} (hp : 0 < p)
    {μ : TemperedDistribution (V p) ℂ} {A B : Set (V p)} {ω η : V p} {R S : ℕ → ℝ}
    (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B)
    (hμ : LocalAtoms μ A) (hν : LocalAtoms (𝓕 μ) B)
    (hω : ‖ω‖ = 1) (hη : ‖η‖ = 1) (hR : HalfBallCount A ω R) (hS : HalfBallCount B η S) :
    ∃ M : ℕ, ∀ y : V p, (A ∩ Metric.ball y 1).ncard ≤ M ∧ (B ∩ Metric.ball y 1).ncard ≤ M :=
  both_carriers_of_fourier_patch_estimate hp (fourier_patch_estimate p) hA hB hμ hν hω hη hR hS

end HalfBall
