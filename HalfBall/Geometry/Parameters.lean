module

public import HalfBall.Geometry.Patches
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Finset
open scoped InnerProductSpace
variable {p : ℕ}

theorem choose_fine_mesh {B : Set (V p)} (hB : LocallyFiniteSites B) (s η : V p)
    {d R : ℝ} (hd : 0 < d) (F : Finset (V p)) :
    ∃ n : ℕ, 0 < n ∧
      (∀ b ∈ B, ‖b-s‖ ≤ R → ⟪η,b-s⟫_ℝ ≠ 0 → Real.sqrt p * (d/n) < |⟪η,b-s⟫_ℝ|) ∧
      ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ‖a+b+c‖ ≤ Real.sqrt p*(3*(d/n)) → a+b+c=0 := by
  classical
  let L := (hB _ (isCompact_closedBall s R)).toFinset
  obtain ⟨e,he,_,hmin⟩ := finite_gap L (fun x => ⟪η,x-s⟫_ℝ)
  obtain ⟨g,hg,_,hgap⟩ := finite_gap (F ×ˢ F ×ˢ F) (fun z => ‖z.1 + z.2.1 + z.2.2‖)
  obtain ⟨n,hn⟩ := exists_nat_gt (3*Real.sqrt p*d/min e g + 1)
  have hm := lt_min he hg
  have hpos : 0 ≤ 3*Real.sqrt p*d/min e g := by positivity
  have hn' : (0 : ℝ) < n := by linarith
  have hmesh : Real.sqrt p*(3*(d/n)) < min e g := by
    have h := (div_lt_iff₀ hm).mp (show 3*Real.sqrt p*d/min e g < n by linarith)
    field_simp
    nlinarith
  refine ⟨n,by exact_mod_cast hn',?_,?_⟩
  · intro b hb hr hz
    have hbl : b ∈ L := (Set.Finite.mem_toFinset _).mpr ⟨hb,by simpa [Metric.mem_closedBall,dist_eq_norm] using hr⟩
    have hbound := (hmesh.trans_le (min_le_left ..)).trans_le (hmin b hbl hz)
    nlinarith [mul_nonneg (Real.sqrt_nonneg (p : ℝ)) (div_nonneg hd.le hn'.le)]
  · intro a ha b hb c hc h
    by_contra heq
    have hbound := hgap (a,b,c) (mem_product.mpr ⟨ha,mem_product.mpr ⟨hb,hc⟩⟩)
      (norm_ne_zero_iff.mpr heq)
    simp only [abs_norm] at hbound
    linarith [hmesh.trans_le (min_le_right e g)]

theorem coarse_mesh {w d : ℝ} (hd : 0 < d) (hw : 2*d ≤ w) :
    ∃ m : ℕ, (m : ℝ)*d ≤ w ∧ w/2 ≤ m*d := by
  refine ⟨⌊w/d⌋₊,?_,?_⟩
  · exact (le_div_iff₀ hd).mp (Nat.floor_le (div_nonneg (by linarith) hd.le))
  · have hf := (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one (w/d))
    linarith

/-- Quantitative contradiction after sampling: the independent cells occupy
at least kΛ/(16D·4^p) volume in their disjoint closed inner boxes. -/
theorem volume_accounting (p m n k D : ℕ) {w d Λ a : ℝ} (hd : 0 < d)
    (hw : 0 < w) (hΛ : 0 < Λ) (hn : 0 < n) (hcover : w/2 ≤ m*d)
    (I : Finset (Grid p (m*n)))
    (hcount : (k : ℝ)*((Fintype.card (Grid p (m*n)) : ℝ) * (Λ / w^p / 2)) ≤ 8*D*I.card)
    (hpatch : (I.card : ℝ)*((d/n)/2)^p ≤ a) :
    (k : ℝ)*Λ ≤ 16 * D * (4:ℝ)^p * a := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : (Fintype.card (Grid p (m*n)) : ℝ) = ((m:ℝ)*n)^p := by simp [Grid]
  rw [hcard] at hcount
  have hl := mul_le_mul_of_nonneg_right hcount (show 0 ≤ ((d/n)/2)^p by positivity)
  have hr := mul_le_mul_of_nonneg_left hpatch (show 0 ≤ 8*(D:ℝ) by positivity)
  have h1 : (k:ℝ)*Λ/(2*w^p) * ((m:ℝ)*d/2)^p ≤ 8*D*a := calc
    _ = (k * ((m*n : ℝ)^p * (Λ/w^p/2))) * ((d/n)/2)^p := by
      simp only [mul_pow,div_pow]
      field_simp
    _ ≤ _ := hl
    _ ≤ _ := by linarith only [hr]
  have h2 : (w/4)^p ≤ ((m:ℝ)*d/2)^p := pow_le_pow_left₀ (by positivity) (by linarith) p
  have h3 := (mul_le_mul_of_nonneg_left h2 (show 0 ≤ (k:ℝ)*Λ/(2*w^p) by positivity)).trans h1
  rw [div_pow] at h3
  have hc : (k:ℝ)*Λ/(2*w^p) * (w^p/4^p) = k*Λ/(2*4^p) := by field_simp
  rw [hc] at h3
  have h4 := (div_le_iff₀ (by positivity)).mp h3
  linarith only [h4]

end HalfBall
