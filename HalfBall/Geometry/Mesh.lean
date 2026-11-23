module

public import HalfBall.Scales
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Finset MeasureTheory
open scoped Pointwise
variable {p m n : ℕ}

abbrev Grid (p m : ℕ) := Fin p → Fin m

def corner (t : ℝ) (v : Grid p m) : V p := WithLp.toLp 2 (fun k => t * (v k).val)

@[simp] theorem corner_apply (t : ℝ) (v : Grid p m) (i) : corner t v i = t * (v i).val := rfl

def Near (x y : V p) (r : ℝ) : Prop := ∀ i, |x i-y i| ≤ r

theorem norm_le_of_coords (x : V p) {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, |x i| ≤ r) :
    ‖x‖ ≤ Real.sqrt p * r := by
  have hsum : ∑ i, (x i)^2 ≤ ∑ _i : Fin p, r^2 := by
    apply sum_le_sum
    intro i _
    simpa using pow_le_pow_left₀ (abs_nonneg _) (h i) 2
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have he := EuclideanSpace.real_norm_sq_eq x
  have hs := Real.sq_sqrt (Nat.cast_nonneg p)
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
  rw [he,mul_pow,hs]
  exact hsum

theorem coord_le_norm (x : V p) (i : Fin p) : |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i

noncomputable def nearGrid (m : ℕ) (t : ℝ) (z : V p) (r : ℝ) : Finset (Grid p m) := by
  classical
  exact univ.filter fun w => Near (corner t w) z r

@[simp] theorem mem_nearGrid (w : Grid p m) (t : ℝ) (z : V p) (r : ℝ) :
    w ∈ nearGrid m t z r ↔ Near (corner t w) z r := by classical simp [nearGrid]

/-- A coordinate window of radius b grid steps contains at most 2b+2
possible integer indices on each axis, independently of its centre. -/
theorem card_nearGrid (m b : ℕ) {t r : ℝ} (ht : 0 < t) (hr : r ≤ b*t) (z : V p) :
    (nearGrid m t z r).card ≤ (2*b+2)^p := by
  classical
  let lo (i : Fin p) := ⌊z i/t⌋ - (b : ℤ)
  let hi (i : Fin p) := ⌊z i/t⌋ + b + 1
  let choices (i : Fin p) := Icc (lo i) (hi i)
  let embed (v : Grid p m) (i : Fin p) : ℤ := (v i).val
  have hinj : Function.Injective embed := by
    intro u v h; funext i; apply Fin.ext; exact Int.ofNat_inj.mp (congrFun h i)
  have hmap : Set.MapsTo embed (↑(nearGrid m t z r)) (↑(Fintype.piFinset choices)) := by
    intro v hv
    apply Fintype.mem_piFinset.mpr
    intro i
    have hh := abs_le.mp (((mem_nearGrid ..).mp hv) i)
    simp only [corner_apply] at hh
    have h1 : z i/t - b ≤ (v i).val := by
      rw [sub_le_iff_le_add,div_le_iff₀ ht]; nlinarith [hh.2,hh.1]
    have h2 : ((v i).val : ℝ) ≤ z i/t + b := by
      rw [← sub_le_iff_le_add,le_div_iff₀ ht]; nlinarith [hh.2,hh.1]
    apply mem_Icc.mpr
    constructor
    · change ⌊z i/t⌋ - (b : ℤ) ≤ ((v i).val : ℤ)
      exact_mod_cast (by linarith [Int.floor_le (z i/t)] : (⌊z i/t⌋ : ℝ) - b ≤ (v i).val)
    · change ((v i).val : ℤ) ≤ ⌊z i/t⌋ + b + 1
      exact_mod_cast (by linarith [Int.lt_floor_add_one (z i/t)] : ((v i).val : ℝ) ≤ (⌊z i/t⌋ : ℝ)+b+1)
  have hcard (i : Fin p) : (choices i).card = 2*b+2 := by
    dsimp only [choices]
    rw [Int.card_Icc]
    dsimp [hi,lo]
    omega
  simpa [Fintype.card_piFinset,hcard] using card_le_card_of_injOn embed hmap hinj.injOn

def coarse (hn : 0 < n) (v : Grid p (m*n)) : Grid p m :=
  fun i => ⟨(v i).val / n, (Nat.div_lt_iff_lt_mul hn).mpr (v i).isLt⟩

theorem coarse_error {d : ℝ} (hd : 0 < d) (hn : 0 < n) (v : Grid p (m*n)) (i : Fin p) :
    0 ≤ corner (d/n) v i - corner d (coarse hn v) i ∧
      corner (d/n) v i - corner d (coarse hn v) i < d := by
  change 0 ≤ d/n*(v i).val - d*((v i).val/n : ℕ) ∧ d/n*(v i).val - d*((v i).val/n : ℕ) < d
  have hdecomp : ((v i).val : ℝ) = n * (((v i).val / n : ℕ) : ℝ) + ((v i).val % n : ℕ) := by
    exact_mod_cast (Nat.div_add_mod (v i).val n).symm
  have hmod : (((v i).val % n : ℕ) : ℝ) < n := by exact_mod_cast Nat.mod_lt (v i).val hn
  have hreal : (0 : ℝ) < n := by exact_mod_cast hn
  constructor <;> field_simp <;> nlinarith [mul_nonneg hd.le (Nat.cast_nonneg ((v i).val % n)),
    mul_pos hd (sub_pos.mpr hmod), congrArg (d*·) hdecomp]

/-- The closed inner half of a fine cell. Its side is t/2. -/
def innerBox (o : V p) (t : ℝ) (v : Grid p m) : Set (V p) :=
  {x | ∀ i, x i ∈ Set.Icc (o i + corner t v i + t/4) (o i + corner t v i + 3*t/4)}

theorem innerBox_volume (o : V p) {t : ℝ} (ht : 0 < t) (v : Grid p m) :
    volume (innerBox o t v) = ENNReal.ofReal ((t/2)^p) := by
  let lo i := o i + corner t v i + t/4
  let hi i := o i + corner t v i + 3*t/4
  have hp := PiLp.volume_preserving_ofLp (Fin p)
  have he : innerBox o t v = (WithLp.ofLp : V p → Fin p → ℝ) ⁻¹' Set.Icc lo hi := by
    ext x
    exact forall_and
  rw [he]
  rw [hp.measure_preimage (measurableSet_Icc.nullMeasurableSet),Real.volume_Icc_pi]
  have hw (i) : hi i - lo i = t/2 := by dsimp [hi,lo]; ring
  simp [hw,ENNReal.ofReal_pow (by positivity : 0 ≤ t/2)]

theorem innerBox_patch (o : V p) {t : ℝ} (ht : 0 < t) (v : Grid p m) : IsPatch (innerBox o t v) := by
  refine ⟨⟨1, fun _ i => o i + corner t v i + t/4,
    fun _ i => o i + corner t v i + 3*t/4,?_⟩,?_⟩
  · ext; simp [innerBox]
  · rw [innerBox_volume o ht v]; positivity

theorem innerBox_disjoint (o : V p) {t : ℝ} (ht : 0 < t) {u v : Grid p m} (hne : u ≠ v) :
    Disjoint (innerBox o t u) (innerBox o t v) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hne; funext i
  have hu := hx i; have hv := hy i
  change _ ≤ x i ∧ x i ≤ _ at hu hv
  simp only [corner_apply] at hu hv
  apply Fin.ext; by_contra! h
  rcases lt_or_gt_of_ne h with h | h
  · have h' : ((u i).val : ℝ)+1 ≤ (v i).val := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_left h' ht.le,hu.2,hv.1]
  · have h' : ((v i).val : ℝ)+1 ≤ (u i).val := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_left h' ht.le,hv.2,hu.1]

end HalfBall
