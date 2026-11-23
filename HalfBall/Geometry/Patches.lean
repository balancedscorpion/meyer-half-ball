module

public import HalfBall.Geometry.FineGraph
public import HalfBall.Geometry.Offsets
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Filter Finset MeasureTheory
open scoped InnerProductSpace Pointwise
variable {p m n : ℕ}

noncomputable def gridOrigin (p : ℕ) (r : ℝ) : V p := WithLp.toLp 2 (fun _ => -r/2)

theorem innerBox_in_cube {R d : ℝ} (hd : 0 < d) (hn : 0 < n)
    (hwidth : (m : ℝ)*d ≤ R/(3*Real.sqrt p)) (v : Grid p (m*n)) :
    innerBox (gridOrigin p (m*d)) (d/n) v ⊆ cube p R := by
  intro x hx i
  have h := hx i
  change -(m*d)/2 + d/n*(v i).val + d/n/4 ≤ x i ∧ x i ≤ -(m*d)/2 + d/n*(v i).val + 3*(d/n)/4 at h
  apply abs_le.mpr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : (v i).val + (1 : ℝ) ≤ (m : ℝ)*n := by exact_mod_cast (v i).isLt
  have hlast : d/n * ((v i).val + (1 : ℝ)) ≤ m*d := calc
    _ ≤ d/n * ((m : ℝ)*n) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by field_simp
  have hr : R/(6*Real.sqrt p) = (R/(3*Real.sqrt p))/2 := by ring
  rw [hr]
  have hstart : 0 ≤ d/n * (v i).val := by positivity
  have hstep : 0 ≤ d/n := by positivity
  constructor <;> linarith [h.1,h.2]

theorem cube_diff_norm (hp : 0 < p) {R : ℝ} (hR : 0 < R) {x y : V p}
    (hx : x ∈ cube p R) (hy : y ∈ cube p R) : ‖x-y‖ ≤ R/3 := by
  have h : ‖x-y‖ ≤ Real.sqrt p * (2*(R/(6*Real.sqrt p))) := by
    apply norm_le_of_coords _ (by positivity)
    intro i
    have h1 := abs_le.mp (hx i); have h2 := abs_le.mp (hy i)
    change |x i-y i| ≤ _
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hs : 0 < Real.sqrt (p : ℝ) := by positivity
  convert h using 1
  field_simp
  ring

theorem box_contact {o x y : V p} {t : ℝ} (ht : 0 < t) {v w : Grid p m}
    (hx : x ∈ innerBox o t v) (hy : y ∈ innerBox o t w) :
    Near (corner t v) (corner t w + (x-y)) t := by
  intro i
  obtain ⟨hx,hx'⟩ := hx i
  obtain ⟨hy,hy'⟩ := hy i
  change |corner t v i - (corner t w i + (x i-y i))| ≤ t
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem coarse_contact {d : ℝ} (hd : 0 < d) (hn : 0 < n) {v w : Grid p (m*n)} {h : V p}
    (hf : Near (corner (d/n) v) (corner (d/n) w+h) (d/n)) :
    Near (corner d (coarse hn v)) (corner d (coarse hn w)+h) (2*d) := by
  intro i
  have hv := coarse_error hd hn v i
  have hw := coarse_error hd hn w i
  have he := abs_le.mp (hf i)
  simp only [PiLp.add_apply] at he ⊢
  have hsmall : d/n ≤ d := div_le_self hd.le (by exact_mod_cast hn)
  exact abs_le.mpr ⟨by linarith [he.1,hv.2,hw.1],by linarith [he.2,hv.1,hw.2]⟩

/-- Order selected cells by the height of their grid corner. Choosing the
fine mesh below the smallest nonzero projection excludes negative-height
offsets even between two cells whose height ranges overlap. -/
theorem ordered_cells_bound {B : Set (V p)} (hB : LocallyFiniteSites B) (hp : 0 < p)
    {a : ℝ} (ha : 0 ≤ a)
    (patch : ∀ s ∈ B, ∀ (l : ℕ) (E : Fin l → Set (V p)), (∀ i, IsPatch (E i)) →
      (∀ i, differencesAt s (E i) (E i) ∩ B = {s}) →
      (∀ i k, k < i → differencesAt s (E i) (E k) ∩ B = ∅) →
      ∑ i, volume (E i) ≤ ENNReal.ofReal a)
    {s η : V p} (hs : s ∈ B ∩ halfSpace η) (hη : ‖η‖ = 1)
    {R d : ℝ} (hd : 0 < d) (hR : 0 < R) (hsR : ‖s‖ ≤ R/2)
    (hn : 0 < n) (hwidth : (m : ℝ)*d ≤ R/(3*Real.sqrt p))
    (hisol : ∀ b ∈ B, b ≠ s → Real.sqrt p * (d/n) < ‖b-s‖)
    (hheight : ∀ b ∈ B, ‖b-s‖ ≤ R → ⟪η,b-s⟫_ℝ ≠ 0 → Real.sqrt p*(d/n) < |⟪η,b-s⟫_ℝ|)
    (X₀ : Finset (V p)) (I : Finset (Grid p (m*n)))
    (hi : (fineGraph (m*n) (d/n) (anchoredOffsets (sites hB η R \ X₀) s η R)
      (anchored_symmetric _ _ _ _)).IsIndepSet (↑I))
    (hbad : ∀ v ∈ I, ∀ w ∈ I, coarse hn w ∉
      coarsePartners m d (anchoredOffsets X₀ s η R) (coarse hn v)) :
    (I.card : ℝ) * ((d/n)/2)^p ≤ a := by
  classical
  let t : ℝ := d/n
  have ht : 0 < t := by dsimp [t]; positivity
  let o := gridOrigin p (m*d)
  let f : Fin I.card ≃ I := (Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
  let height (j : Fin I.card) := ⟪η,corner t (f j).val⟫_ℝ
  let v (j : Fin I.card) := (f (Tuple.sort height j)).val
  let E (j : Fin I.card) := innerBox o t (v j)
  have hv (j) : v j ∈ I := (f (Tuple.sort height j)).property
  have mono : Monotone (fun j => ⟪η,corner t (v j)⟫_ℝ) := Tuple.monotone_sort height
  have vi : Function.Injective v := Subtype.val_injective.comp (f.injective.comp (Tuple.sort height).injective)
  have hsmall {i k} {x y : V p} (hx : x ∈ E i) (hy : y ∈ E k) :
      ‖(x-y) - (corner t (v i)-corner t (v k))‖ ≤ Real.sqrt p*t := by
    apply norm_le_of_coords _ ht.le
    intro j
    have hc := abs_le.mp (box_contact ht hx hy j)
    simp only [PiLp.sub_apply,PiLp.add_apply] at hc ⊢
    exact abs_le.mpr ⟨by linarith [hc.2],by linarith [hc.1]⟩
  have estimate := patch s hs.1 I.card E (fun j => innerBox_patch o ht _) (by
    intro i
    ext b
    constructor
    · rintro ⟨⟨x,hx,y,hy,rfl⟩,hb⟩
      by_contra hne
      have h := hisol _ hb hne
      have hdist : s+x-y-s = x-y := by abel
      rw [hdist] at h
      exact h.not_ge (by simpa using hsmall hx hy)
    · rintro rfl
      have hnon : (E i).Nonempty := by
        by_contra! he
        have hpos := (innerBox_patch o ht (v i)).2
        change 0 < volume (E i) at hpos
        simp [he] at hpos
      obtain ⟨x,hx⟩ := hnon
      exact ⟨⟨x,hx,x,hx,by simp⟩,hs.1⟩) (by
    intro i k hik
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro b ⟨⟨x,hx,y,hy,rfl⟩,hb⟩
    let h := x-y
    have hbs : s+x-y = s+h := by dsimp [h]; abel
    have hdiff : (s+h)-s = h := by abel
    change s+x-y ∈ B at hb
    rw [hbs] at hb
    have hne : h ≠ 0 := fun hz => (Set.disjoint_left.mp (innerBox_disjoint o ht
      (vi.ne hik.ne'))) hx (sub_eq_zero.mp hz ▸ hy)
    have hwinx := innerBox_in_cube hd hn hwidth (v i) hx
    have hwiny := innerBox_in_cube hd hn hwidth (v k) hy
    have hr := cube_diff_norm hp hR hwinx hwiny
    have hproj : 0 ≤ ⟪η,h⟫_ℝ := by
      by_contra! hneg
      have hgap := hheight _ hb (by rw [hdiff]; linarith [hr] : ‖s+h-s‖ ≤ R) (by rw [hdiff]; exact hneg.ne)
      rw [hdiff,abs_of_neg hneg] at hgap
      have hi' := (abs_real_inner_le_norm η _).trans (mul_le_mul_of_nonneg_left (hsmall hx hy) (norm_nonneg _))
      rw [hη,one_mul,inner_sub_right,inner_sub_right] at hi'
      have hmon := mono hik.le
      change ⟪η,corner t (v k)⟫_ℝ ≤ ⟪η,corner t (v i)⟫_ℝ at hmon
      change ⟪η,x-y⟫_ℝ < 0 at hneg
      change Real.sqrt p*t < -⟪η,x-y⟫_ℝ at hgap
      simp only [inner_sub_right] at hi' hgap
      linarith [(abs_le.mp hi').1]
    have hsite : s+h ∈ sites hB η R := by
      rw [mem_sites]
      refine ⟨hb,?_,?_⟩
      · change 0 ≤ ⟪η,s+h⟫_ℝ; rw [inner_add_right]; exact add_nonneg hs.2 hproj
      · rw [Metric.mem_closedBall,dist_zero_right]
        exact (norm_add_le ..).trans (by linarith : ‖s‖+‖h‖ ≤ R)
    have hrec (X : Finset (V p)) (hm : s+h ∈ X) : h ∈ anchoredOffsets X s η R := by
      apply mem_anchoredOffsets.mpr
      refine ⟨s+h,hm,by simpa using hne,?_,?_,Or.inl hdiff.symm⟩
      · simpa using hproj
      · rw [hdiff]; exact Set.sub_mem_sub hwinx hwiny
    have hcontact := box_contact ht hx hy
    by_cases hm : s+h ∈ X₀
    · exact hbad _ (hv k) _ (hv i) (mem_biUnion.mpr ⟨h,hrec _ hm,(mem_nearGrid ..).mpr (coarse_contact hd hn hcontact)⟩)
    · exact hi (hv k) (hv i) (vi.ne hik.ne) ⟨vi.ne hik.ne,h,hrec _ (mem_sdiff.mpr ⟨hsite,hm⟩),hcontact⟩)
  have hvol (i) : volume (E i) = ENNReal.ofReal ((t/2)^p) := innerBox_volume o ht (v i)
  simp only [hvol,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at estimate
  apply (ENNReal.ofReal_le_ofReal_iff ha).mp
  simpa [ENNReal.ofReal_mul] using estimate

end HalfBall
