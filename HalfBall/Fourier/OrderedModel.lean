module

public import HalfBall.Fourier.AtomicModel
public import HalfBall.Fourier.PatchSampling
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Fourier

open MeasureTheory Metric Set Finset FourierTransform
variable {p m : ℕ}

private theorem compact_differences {E F : Set (V p)} (hE : IsCompact E) (hF : IsCompact F) (s : V p) :
    IsCompact (differencesAt s E F) := by
  rw [differencesAt,← Set.image_prod]
  exact (hE.prod hF).image (by fun_prop)

/-- Rapid decay of a finite list of unwanted atoms on a compact region
disjoint from those atoms. The separation constant may depend on the region. -/
private theorem unwanted_sum (h : SchwartzMap (V p) ℂ) (N : ℕ) {K : Set (V p)} (hK : IsCompact K)
    (U : Finset (V p)) (w : V p → ℂ) (hU : ∀ u ∈ U, u ∉ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ q ∈ K,
      R^N*‖∑ u ∈ U, w u * h (R • (u-q))‖ ≤ C := by
  classical
  let A := SchwartzMap.seminorm ℂ N 0 h
  have hterm (u) (hu : u ∈ U) : ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 0 < R → ∀ q ∈ K,
      R^N*‖w u*h (R • (u-q))‖ ≤ c := by
    obtain ⟨δ,hδ,hsep⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl u (hU u hu)
    refine ⟨‖w u‖*(A/δ^N),mul_nonneg (norm_nonneg _) (div_nonneg (apply_nonneg _ _) (by positivity)),?_⟩
    intro R hR q hq
    have hd : δ ≤ ‖u-q‖ := by
      by_contra! hn; exact hsep (show q ∈ ball u δ by simpa [mem_ball,dist_eq_norm,norm_sub_rev] using hn) hq
    have hh := SchwartzMap.le_seminorm ℂ N 0 h (R • (u-q))
    simp only [norm_iteratedFDeriv_zero,norm_smul,Real.norm_eq_abs,abs_of_pos hR,mul_pow] at hh
    rw [norm_mul, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (le_div_iff₀ (pow_pos hδ _)).mpr
    calc
      _ = R^N * δ^N * ‖h (R • (u-q))‖ := by ring
      _ ≤ R^N * ‖u-q‖^N * ‖h (R • (u-q))‖ := by gcongr
      _ ≤ A := hh
  choose c hc hb using fun u : U => hterm u u.property
  refine ⟨∑ u : U, c u, sum_nonneg (fun i _ => hc i),?_⟩
  intro R hR q hq
  rw [← Finset.sum_attach]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) (pow_nonneg hR.le N)).trans ?_
  rw [Finset.mul_sum]
  exact sum_le_sum (fun i _ => hb i R hR q hq)

/-- The triangular approximation uses the full finite spectral model above
the diagonal, the isolated anchor alone on the diagonal, and zero below it. -/
def blockModel (h : SchwartzMap (V p) ℂ) (s : V p) (U : Finset (V p)) (w : V p → ℂ)
    (R : ℝ) (i j : Fin m) (q : V p) : ℂ :=
  if i < j then ∑ u ∈ U, w u * h (R • (u-q))
  else if i = j then w s * h (R • (s-q)) else 0

theorem ordered_model {T : TemperedDistribution (V p) ℂ} {B : Set (V p)}
    (hB : LocallyFiniteSites B) (hT : LocalAtoms T B) (h : SchwartzMap (V p) ℂ)
    (N : ℕ) {s : V p} (hs : s ∈ B) (E : Fin m → Set (V p)) (hE : ∀ i, IsCompact (E i))
    (hdiag : ∀ i, differencesAt s (E i) (E i) ∩ B = {s})
    (hlower : ∀ i j, j < i → differencesAt s (E i) (E j) ∩ B = ∅) :
    ∃ (U : Finset (V p)) (w : V p → ℂ) (C : ℝ), w s ≠ 0 ∧ 0 ≤ C ∧
      ∀ {R : ℝ} (hR : 1 ≤ R) (i j : Fin m), ∀ x ∈ E i, ∀ y ∈ E j,
      R^N * ‖T (sample h R (by linarith) (s+x-y)) - blockModel h s U w R i j (s+x-y)‖ ≤ C := by
  classical
  let D i j := differencesAt s (E i) (E j)
  let K := ⋃ i, ⋃ j, D i j
  have hK : IsCompact K := isCompact_iUnion (fun i => isCompact_iUnion (fun j => compact_differences (hE i) (hE j) s))
  obtain ⟨Q,hQ,hQK⟩ := hK.isBounded.subset_closedBall_lt ‖s‖ 0
  obtain ⟨U,w,C,hC,hUB,hW,hmodel⟩ := compact_atomic_model hB hT h ((norm_nonneg _).trans hQ.le) N
  obtain ⟨hsU,hsw⟩ := hW s hs hQ.le
  let sumAt (R : ℝ) (q : V p) := ∑ u ∈ U, w u * h (R • (u-q))
  have hpair (i j : Fin m) : ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 0 < R → ∀ q ∈ D i j,
      R^N * ‖sumAt R q - blockModel h s U w R i j q‖ ≤ c := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact ⟨0,le_rfl,fun _ _ _ _ => by simp [sumAt,blockModel,hij]⟩
    · obtain ⟨c,hc,hh⟩ := unwanted_sum h N (compact_differences (hE i) (hE i) s) (U.erase s) w (by
        intro u hu hd
        have hm : u ∈ differencesAt s (E i) (E i) ∩ B := ⟨hd,hUB (mem_of_mem_erase hu)⟩
        rw [hdiag] at hm
        exact (ne_of_mem_erase hu) hm)
      refine ⟨c,hc,fun R hR q hq => ?_⟩
      have hadd := sum_erase_add (s := U) (fun u => w u * h (R • (u-q))) hsU
      simp only [blockModel,lt_irrefl,ite_false,ite_true,sumAt,← hadd,add_sub_cancel_right]
      exact hh R hR q hq
    · obtain ⟨c,hc,hh⟩ := unwanted_sum h N (compact_differences (hE i) (hE j) s) U w (by
        intro u hu hd
        have hm : u ∈ differencesAt s (E i) (E j) ∩ B := ⟨hd,hUB hu⟩
        rwa [hlower i j hji] at hm)
      refine ⟨c,hc,fun R hR q hq => ?_⟩
      simpa [blockModel,not_lt_of_gt hji,hji.ne',sumAt] using hh R hR q hq
  choose c hc hh using fun k : Fin m × Fin m => hpair k.1 k.2
  refine ⟨U,w,C+∑ k, c k,hsw,add_nonneg hC (sum_nonneg fun k _ => hc k),?_⟩
  intro R hR i j x hx y hy
  let q := s+x-y
  have hq : q ∈ D i j := ⟨x,hx,y,hy,rfl⟩
  have hnorm : ‖q‖ ≤ Q := by simpa using hQK (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,hq⟩⟩)
  have h1 := hmodel hR q hnorm
  have h2 := hh (i,j) R (by linarith) q hq
  have htri := norm_sub_le_norm_sub_add_norm_sub (T (sample h R (by linarith) q)) (sumAt R q)
    (blockModel h s U w R i j q)
  refine (mul_le_mul_of_nonneg_left htri (by positivity)).trans ?_
  rw [mul_add]
  exact add_le_add h1 (h2.trans (single_le_sum (fun k _ => hc k) (mem_univ _)))

end HalfBall.Fourier
