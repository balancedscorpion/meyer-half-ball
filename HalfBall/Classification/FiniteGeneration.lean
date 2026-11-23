/-
The Stone–Weierstrass argument adapts AppendixA/PhaseGeneration.lean in
the pinned lev-olevskii-lattice-cover dependency. See LICENSES/lev-olevskii-lattice-cover-MIT.txt.
-/
module
public import HalfBall.Classification.PhaseDifference
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Tactic
public section
noncomputable section
namespace HalfBall.Classification
open MeyerGeneralProblem.LevOlevskii Set Filter Metric FourierTransform Finset
open scoped Topology ComplexConjugate FourierTransform

private abbrev character {d : ℕ} (u t : Space d) : ℂ := (frequencyPhase u t : ℂ)

private theorem character_add {d : ℕ} (u v t : Space d) :
    character (u+v) t = character u t * character v t := by
  change (Real.fourierChar (inner ℝ t (u+v)) : ℂ) = _
  rw [inner_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]
  rfl

private theorem character_neg {d : ℕ} (u t : Space d) :
    character (-u) t = conj (character u t) := by
  change (Real.fourierChar (inner ℝ t (-u)) : ℂ) = _
  rw [inner_neg_right, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

private theorem character_half_turn {d : ℕ} (u : Space d) (hu : u ≠ 0) :
    ∃ t, character u t = -1 := by
  have hpos := real_inner_self_pos.mpr hu
  refine ⟨(2 * inner ℝ u u)⁻¹ • u, ?_⟩
  change (Real.fourierChar (inner ℝ ((2 * inner ℝ u u)⁻¹ • u) u) : ℂ) = -1
  rw [real_inner_smul_left, Real.fourierChar_apply]
  have hh : 2 * Real.pi * ((2 * inner ℝ u u)⁻¹ * inner ℝ u u) = Real.pi := by
    field_simp
  rw [hh, Complex.exp_pi_mul_I]

private theorem character_sum_nonpositive {d : ℕ} {ι : Type*} (s : Finset ι)
    (u : ι → Space d) (hu : ∀ i ∈ s, u i ≠ 0) (c : ι → ℂ) :
    ∃ t, (∑ i ∈ s, c i * character (u i) t).re ≤ 0 := by
  classical
  induction s using Finset.induction generalizing c with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨v, hv⟩ := character_half_turn _ (hu i (Finset.mem_insert_self ..))
    obtain ⟨t, ht⟩ := ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
      (fun j => c j * (1 + character (u j) v))
    by_contra! h
    have hh := add_pos (h t) (h (t+v))
    rw [← Complex.add_re, ← Finset.sum_add_distrib] at hh
    have hadd (j) : c j * character (u j) t + c j * character (u j) (t+v) =
        (c j * (1 + character (u j) v)) * character (u j) t := by
      simp only [character, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
    simp_rw [hadd] at hh
    rw [Finset.sum_insert hi, hv] at hh
    simpa using (not_lt_of_ge ht) (by simpa using hh)

private abbrev Hull {d : ℕ} (B : Set (Space d)) :=
  closure (range (fun t : Space d => fun i : B => frequencyPhase i.val t))

private def orbit {d : ℕ} (B : Set (Space d)) (t : Space d) : Hull B :=
  ⟨_, subset_closure (mem_range_self t)⟩

private def coordinate {d : ℕ} {B : Set (Space d)} (i : B) : C(Hull B, ℂ) where
  toFun z := (z.val i : ℂ)
  continuous_toFun := continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)

/-- A polynomial on the orbit has a finite expansion in the indicated
additive subgroup. Allowing repeated frequencies avoids choosing an ordering. -/
private def windowAlgebra {d : ℕ} (B : Set (Space d)) (G : AddSubgroup (Space d)) :
    StarSubalgebra ℂ C(Hull B, ℂ) where
  carrier := {f | ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (u : ι → G), ∀ t : Space d,
    f (orbit B t) = ∑ j, c j * character (u j).val t}
  algebraMap_mem' r := ⟨Unit, inferInstance, fun _ => r, fun _ => 0, fun t => by
    simp [character, frequencyPhase, orbit]⟩
  add_mem' := by
    rintro f g ⟨I,hI,c,u,hf⟩ ⟨J,hJ,b,v,hg⟩
    exact ⟨I ⊕ J, inferInstance, Sum.elim c b, Sum.elim u v, fun t => by
      simp [Fintype.sum_sum_type, hf, hg]⟩
  mul_mem' := by
    rintro f g ⟨I,hI,c,u,hf⟩ ⟨J,hJ,b,v,hg⟩
    refine ⟨I × J, inferInstance, fun ij => c ij.1 * b ij.2, fun ij => u ij.1 + v ij.2, fun t => ?_⟩
    simp only [ContinuousMap.mul_apply, hf, hg, Fintype.sum_prod_type, Finset.sum_mul_sum,
      AddSubgroup.coe_add, character_add, mul_comm, mul_assoc, mul_left_comm]
  star_mem' := by
    rintro f ⟨I,hI,c,u,hf⟩
    refine ⟨I,hI, fun i => conj (c i), fun i => -(u i), fun t => ?_⟩
    simp [hf, character_neg]

private theorem phase_distance {d} (u t s : V d) :
    ‖1-(frequencyPhase u (t-s) : ℂ)‖ = ‖(frequencyPhase u t : ℂ)-(frequencyPhase u s : ℂ)‖ := by
  let a : Circle := frequencyPhase u t
  let b : Circle := frequencyPhase u s
  rw [AddChar.map_sub_eq_div,Circle.coe_div]
  change ‖1-(a:ℂ)/b‖ = ‖(a:ℂ)-b‖
  have he : (1-(a:ℂ)/b)*(b:ℂ) = (b:ℂ)-a := by field_simp
  have hh := congrArg norm he
  simpa [norm_mul,norm_sub_rev (b:ℂ) a] using hh

private theorem phase_window_separates {d} {μ : TemperedDistribution (V d) ℂ}
    {A B : Set (V d)} {a : A → ℂ} {b : B → ℂ} {M} (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B)
    (ha : HasLocallyAtomicExpansion μ A a) (hb : HasLocallyAtomicExpansion (𝓕 μ) B b) (cap : BallCap A M) :
    ∃ D : ℝ, 0 < D ∧ ∀ z ∈ Hull B, ∀ w ∈ Hull B,
      (∀ i : B, ‖i.val‖ ≤ D → z i = w i) → z = w := by
  classical
  obtain ⟨D,hD,F,hF,hcontrol⟩ := phase_difference_control hA hB ha hb cap
  refine ⟨D,hD,fun z hz w hw he => funext (fun x => ?_)⟩
  obtain ⟨C,hC⟩ := hcontrol x
  let distAt (i : B) (zw : (B → Circle) × (B → Circle)) := ‖(zw.1 i : ℂ)-(zw.2 i : ℂ)‖
  have hc (i : B) : Continuous (distAt i) := by unfold distAt; fun_prop
  let Q := {zw : (B → Circle) × (B → Circle) | ‖b x‖ * distAt x zw ≤ (∑ i ∈ F, ‖b i‖ * distAt i zw)*C}
  have hQ : IsClosed Q := isClosed_le (continuous_const.mul (hc _))
    ((continuous_finsetSum _ fun i _ => continuous_const.mul (hc i)).mul continuous_const)
  let E := range (fun t : V d => fun i : B => frequencyPhase i.val t)
  have hsub : E ×ˢ E ⊆ Q := by
    rintro ⟨v₁,v₂⟩ ⟨⟨t,ht⟩,⟨s,hs⟩⟩
    change _ = v₁ at ht
    change _ = v₂ at hs
    subst v₁ v₂
    simpa only [Q,mem_ofPred_eq,distAt,phase_distance] using hC (t-s)
  have hmem : (z,w) ∈ closure (E ×ˢ E) := by
    rw [closure_prod_eq]
    exact ⟨hz,hw⟩
  have hzw := closure_minimal hsub hQ hmem
  have hzero i (hi : i ∈ F) : distAt i (z,w) = 0 := by simp [distAt,he i (hF i hi)]
  change ‖b x‖ * distAt x (z,w) ≤ (∑ i ∈ F, ‖b i‖ * distAt i (z,w))*C at hzw
  have hz' : distAt x (z,w) = 0 := by
    have hsum : ∑ i ∈ F, ‖b i‖ * distAt i (z,w) = 0 := sum_eq_zero fun i hi => by rw [hzero i hi,mul_zero]
    rw [hsum,zero_mul] at hzw
    exact le_antisymm (le_of_not_gt (fun h => hzw.not_gt (mul_pos (norm_pos_iff.mpr (hb.1 x)) h))) (norm_nonneg _)
  exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp hz'))

/-- A bounded part of the spectrum generates every spectral frequency over
the integers. The proof allows complex weights of arbitrarily small modulus. -/
theorem spectral_window_generates {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    {M : ℕ} (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B)
    (hμ : HasLocallyAtomicExpansion μ A a) (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (cap : BallCap A M) :
    ∃ R : ℝ, 0 < R ∧ B ⊆ AddSubgroup.closure (B ∩ closedBall 0 R) := by
  classical
  obtain ⟨R,hR,hsep⟩ := phase_window_separates hA hB hμ hν cap
  let G := AddSubgroup.closure (B ∩ closedBall 0 R)
  let P := windowAlgebra B G
  let : CompactSpace (Hull B) := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  have hc (i : B) (hi : ‖i.val‖ ≤ R) : coordinate i ∈ P := by
    have hg : i.val ∈ G := AddSubgroup.subset_closure ⟨i.property, by simpa using hi⟩
    exact ⟨Unit,inferInstance,fun _ => 1,fun _ => ⟨i.val,hg⟩,fun t => by simp [coordinate,orbit]⟩
  have hseparates : P.SeparatesPoints := by
    intro z w hzw
    have hdiff : ∃ i : B, ‖i.val‖ ≤ R ∧ z.val i ≠ w.val i := by
      by_contra! hs
      exact hzw (Subtype.ext (hsep z.val z.property w.val w.property hs))
    obtain ⟨i,hi,hd⟩ := hdiff
    refine ⟨coordinate i, ⟨_,hc i hi,rfl⟩, fun he => hd (Subtype.ext he)⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints P hseparates
  refine ⟨R,hR,fun x hx => ?_⟩
  by_contra hnot
  let F := coordinate (⟨x,hx⟩ : B)
  have hcl : F ∈ closure (P : Set C(Hull B,ℂ)) := by rw [← P.topologicalClosure_coe, htop]; trivial
  obtain ⟨g,hg,hclose⟩ := Metric.mem_closure_iff.mp hcl 1 one_pos
  obtain ⟨I,hI,c,u,hg⟩ := hg
  let v (j : I) := (u j).val - x
  have hne (i : I) (_ : i ∈ (Finset.univ : Finset I)) : v i ≠ 0 :=
    sub_ne_zero.mpr fun he => hnot (he ▸ (u i).property)
  obtain ⟨t, ht⟩ := character_sum_nonpositive Finset.univ v hne c
  let m := ∑ j, c j * character (v j) t
  have he (j : I) : character (u j).val t = character (v j) t * character x t := by
    rw [← character_add, sub_add_cancel]
  have hgt : g (orbit B t) = m * character x t := by
    rw [hg, Finset.sum_mul]; simp only [he, mul_assoc]
  have hm := (ContinuousMap.dist_apply_le_dist (f := F) (g := g) (orbit B t)).trans_lt hclose
  change dist (character x t) (g (orbit B t)) < 1 at hm
  rw [hgt, dist_eq_norm, ← one_sub_mul, norm_mul] at hm
  have hm' : ‖1 - m‖ < 1 := by simpa [character] using hm
  have hreal := (Complex.re_le_norm (1-m)).trans_lt hm'
  simp only [Complex.sub_re, Complex.one_re] at hreal
  change m.re ≤ 0 at ht
  linarith

/-- Proposition B.2 for the spectral group. -/
theorem spectral_group_fg {p M} {μ : TemperedDistribution (V p) ℂ} {A B : Set (V p)}
    (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B) (ha : LocalAtoms μ A) (hb : LocalAtoms (𝓕 μ) B)
    (cap : BallCap A M) : (AddSubgroup.closure B).FG := by
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  obtain ⟨D,_,hgen⟩ := spectral_window_generates hA hB ha hb cap
  exact (AddSubgroup.fg_iff _).mpr ⟨_,le_antisymm (AddSubgroup.closure_mono inter_subset_left)
    ((AddSubgroup.closure_le _).mpr hgen),hB _ (isCompact_closedBall _ _)⟩

end HalfBall.Classification
