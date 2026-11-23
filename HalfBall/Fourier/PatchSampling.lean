module

public import HalfBall.Geometry.Mesh
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HalfBall.Fourier

open Finset Metric MeasureTheory Set
variable {p : ℕ}

theorem compact_of_patch {E : Set (V p)} (hE : IsPatch E) : IsCompact E := by
  obtain ⟨⟨n,lo,hi,rfl⟩,_⟩ := hE
  apply isCompact_iUnion
  intro i
  have he : {x : V p | ∀ k, x k ∈ Icc (lo i k) (hi i k)} =
      (WithLp.ofLp : V p → Fin p → ℝ) ⁻¹' Set.Icc (lo i) (hi i) := by ext; exact forall_and
  rw [he]
  exact (PiLp.continuousLinearEquiv 2 ℝ _).toHomeomorph.isCompact_preimage.mpr isCompact_Icc

private theorem separated_cover {E : Set (V p)} (hc : IsCompact E) {r : ℝ} (hr : 0 < r) :
    ∃ Y : Finset (V p), ↑Y ⊆ E ∧ (Y : Set (V p)).Pairwise (fun x y => r ≤ dist x y) ∧
      E ⊆ ⋃ y ∈ Y, ball y (2*r) := by
  classical
  obtain ⟨t,ht,hfin,hcover⟩ := hc.finite_cover_balls hr
  let F := hfin.toFinset
  let sep (D : Finset (V p)) := (D : Set (V p)).Pairwise fun x y => r ≤ dist x y
  let choices := F.powerset.filter sep
  obtain ⟨Y,hY,hmax⟩ := choices.exists_max_image Finset.card (show choices.Nonempty from ⟨∅, by simp [choices,sep]⟩)
  obtain ⟨hsub,hsep⟩ := mem_filter.mp hY
  have hYF := mem_powerset.mp hsub
  refine ⟨Y,fun _ h => ht (hfin.mem_toFinset.mp (hYF h)),hsep,?_⟩
  intro z hz
  obtain ⟨x,hx,hxz⟩ := mem_iUnion₂.mp (hcover hz)
  have hnear : ∃ y ∈ Y, dist x y < r := by
    by_contra! hn
    have hxY : x ∉ Y := fun hh => (not_lt_of_ge (hn x hh)) (by simpa using hr)
    have hsep' : sep (insert x Y) := by
      change (↑(insert x Y) : Set (V p)).Pairwise _
      rw [coe_insert]
      rw [Set.pairwise_insert]
      exact ⟨hsep,fun y hy _ => ⟨hn y hy,dist_comm x y ▸ hn y hy⟩⟩
    have hm := hmax (insert x Y) (mem_filter.mpr ⟨mem_powerset.mpr
      (Finset.insert_subset (hfin.mem_toFinset.mpr hx) hYF),hsep'⟩)
    rw [card_insert_of_notMem hxY] at hm
    omega
  obtain ⟨y,hy,hxy⟩ := hnear
  apply mem_iUnion₂.mpr ⟨y,hy,?_⟩
  exact (dist_triangle z x y).trans_lt (by linarith [show dist z x < r from hxz])

def unitBallVolume (p : ℕ) := volume.real (ball (0 : V p) 1)

theorem unitBallVolume_pos (p : ℕ) : 0 < unitBallVolume p :=
  ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne

/-- A fixed volume per sample at resolution L/R. The number of samples
is the ceiling of the displayed quantity, giving a polynomial upper bound
as well as the lower bound which controls patch volume. -/
theorem sample_patch {E : Set (V p)} (hE : IsCompact E) {L R : ℝ} (hL : 0 < L) (hR : 0 < R) :
    ∃ Y : Finset (V p), ↑Y ⊆ E ∧ (Y : Set (V p)).Pairwise (fun x y => L/R ≤ dist x y) ∧
      Y.card = ⌈volume.real E * R^p / ((2*L)^p * unitBallVolume p)⌉₊ := by
  classical
  let r := L/R
  have hr : 0 < r := div_pos hL hR
  obtain ⟨D,hDE,hsep,hcover⟩ := separated_cover hE hr
  have hvol (x : V p) : volume.real (ball x (2*r)) = (2*r)^p * unitBallVolume p := by
    simp [Measure.real,Measure.addHaar_ball_of_pos volume x (by positivity : 0 < 2*r),
      unitBallVolume,ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*r)^p)]
  have hcount : volume.real E ≤ (D.card:ℝ)*((2*r)^p * unitBallVolume p) := by
    refine (measureReal_mono hcover (measure_biUnion_ne_top D.finite_toSet (fun _ _ => measure_ball_lt_top.ne))).trans ?_
    simpa only [hvol,Finset.sum_const,nsmul_eq_mul] using
      (measureReal_biUnion_finset_le (μ := volume) D (fun x => ball x (2*r)))
  have hratio : volume.real E*R^p / ((2*L)^p * unitBallVolume p) ≤ D.card := by
    apply (div_le_iff₀ (mul_pos (by positivity) (unitBallVolume_pos p))).mpr
    have hh := mul_le_mul_of_nonneg_right hcount (pow_nonneg hR.le p)
    convert hh using 1
    dsimp [r]; rw [mul_div_assoc',div_pow]; field_simp
  obtain ⟨Y,hYD,hcard⟩ := Finset.exists_subset_card_eq (Nat.ceil_le.mpr hratio)
  exact ⟨Y,fun _ h => hDE (hYD h),hsep.mono (fun _ h => hYD h),hcard⟩

end HalfBall.Fourier
