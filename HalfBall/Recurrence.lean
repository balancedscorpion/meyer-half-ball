module

public import HalfBall.Geometry.Offsets
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Filter MeasureTheory
open scoped Topology

/-- A translation of a finite pattern may move each site by a separate error. -/
def PatternReturn {p} (B : Set (V p)) (F : Finset (V p)) (ε : ℝ) (t : V p) : Prop :=
  ∀ f ∈ F, ∃ b ∈ B, dist b (f+t) < ε

private theorem ordered_list {u : Ultrafilter ℕ} {P : ℕ → ℕ → Prop}
    (h : ∀ᶠ i in u, ∀ᶠ j in u, P i j) (n : ℕ) :
    ∀ D : Set ℕ, D ∈ u → ∃ v : Fin n → ℕ,
      (∀ i, v i ∈ D) ∧ ∀ i j, i < j → P (v i) (v j) := by
  induction n with
  | zero => exact fun _ _ => ⟨Fin.elim0, (fun i => i.elim0), (fun i => i.elim0)⟩
  | succ n ih =>
    intro D hD
    obtain ⟨a,ha,haP⟩ := Filter.nonempty_of_mem (inter_mem hD h : D ∩ {i | ∀ᶠ j in u, P i j} ∈ (u : Filter ℕ))
    obtain ⟨v,hv,hpair⟩ := ih (D ∩ {j | P a j}) (inter_mem hD haP)
    refine ⟨Fin.cons a v, Fin.cases ha (fun i => (hv i).1), ?_⟩
    intro i j
    refine Fin.cases (motive := fun i => i < j → P ((Fin.cons (α := fun _ => ℕ) a v) i) ((Fin.cons (α := fun _ => ℕ) a v) j)) ?_ ?_ i
    · cases j using Fin.cases with
      | zero => simp
      | succ j => exact fun _ => (hv j).2
    · intro i hij
      cases j using Fin.cases with
      | zero => exact False.elim ((Fin.not_lt_zero _) hij)
      | succ j => exact hpair i j ((Fin.succ_lt_succ_iff).mp hij)

/-- Lemma A.2. The return set of each finite pattern meets every open ball of
one fixed radius. A free ultrafilter extracts an arbitrarily long ordered
monochromatic list from a hypothetical sequence of holes of growing radii. -/
theorem pattern_recurrence {p} {B : Set (V p)} (hB : LocallyFiniteSites B)
    (hpatch : OrderedPatchBound B) (F : Finset (V p)) (hF : ↑F ⊆ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ z : V p, ∃ t, dist t z < L ∧ PatternReturn B F ε t := by
  classical
  by_contra hn
  push Not at hn
  choose z hz using fun n : ℕ => hn ((n:ℝ)+1) (by positivity)
  let u := Ultrafilter.of (atTop : Filter ℕ)
  have hbad (i : ℕ) : ∀ᶠ j in u, ∃ f ∈ F, ∀ b ∈ B, ε ≤ dist b (f+(z j-z i)) := by
    obtain ⟨N,hN⟩ := exists_nat_gt ‖z i‖
    filter_upwards [(eventually_ge_atTop N).filter_mono (Ultrafilter.of_le _)] with j hj
    have hd : dist (z j-z i) (z j) < (j:ℝ)+1 := by
      rw [dist_eq_norm,show z j-z i-z j = -(z i) by abel,norm_neg]
      have : (N:ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have hh := hz j (z j-z i) hd
    simpa [PatternReturn, not_forall] using hh
  have hrow (i : ℕ) := (Ultrafilter.eventually_exists_mem_iff (f := u) F.finite_toSet).mp (hbad i)
  obtain ⟨f,hf,hh⟩ := (Ultrafilter.eventually_exists_mem_iff (f := u) F.finite_toSet).mp
    (Eventually.of_forall hrow)
  obtain ⟨d,hd,_,hisol⟩ := anchor_isolation hB f
  let w := min d ε / (Real.sqrt p + 1)
  have hw : 0 < w := div_pos (lt_min hd hε) (by positivity)
  have hdiam : Real.sqrt p*w < min d ε := by
    have he : (Real.sqrt p+1)*w = min d ε := by dsimp [w]; field_simp
    linarith
  obtain ⟨a,ha,hbound⟩ := hpatch
  obtain ⟨n,hn⟩ := exists_nat_gt (a/(w/2)^p)
  obtain ⟨v,_,hv⟩ := ordered_list hh n Set.univ univ_mem
  let v0 : Grid p 1 := fun _ => 0
  let x (i : Fin n) := z (v i)
  let E (i : Fin n) := innerBox (x i) w v0
  have hnear {i j} {s t : V p} (hs : s ∈ E i) (ht : t ∈ E j) :
      ‖(f+s-t)-(f+(x i-x j))‖ < min d ε := by
    refine (norm_le_of_coords _ hw.le (fun k => ?_)).trans_lt hdiam
    have h1 := hs k
    have h2 := ht k
    change _ ≤ s k ∧ s k ≤ _ at h1
    change _ ≤ t k ∧ t k ≤ _ at h2
    simp only [corner_apply, v0, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero] at h1 h2
    change |(f k + s k - t k) - (f k + (x i k - x j k))| ≤ w
    apply abs_le.mpr
    constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
  have hdiag (i) : differencesAt f (E i) (E i) ∩ B = {f} := by
    ext b
    constructor
    · rintro ⟨⟨s,hs,t,ht,rfl⟩,hb⟩
      apply Set.mem_singleton_iff.mpr
      by_contra hne
      have hd' := (hnear hs ht).trans_le (min_le_left ..)
      simp only [sub_self,add_zero] at hd'
      exact (not_lt_of_ge (hisol _ hb hne)) hd'
    · rintro rfl
      let s : V p := WithLp.toLp 2 (fun k => x i k+w/4)
      have hs : s ∈ E i := by
        intro k
        change _ ≤ x i k+w/4 ∧ x i k+w/4 ≤ _
        simp only [corner_apply,v0,Fin.val_zero,Nat.cast_zero,mul_zero,add_zero]
        constructor <;> linarith
      exact ⟨⟨s,hs,s,hs,by simp⟩,hF hf⟩
  have hoff (i j : Fin n) (hji : j < i) : differencesAt f (E i) (E j) ∩ B = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨⟨s,hs,t,ht,rfl⟩,hb⟩
    exact (not_lt_of_ge (hv j i hji _ hb)) (by
      rw [dist_eq_norm]; exact (hnear hs ht).trans_le (min_le_right ..))
  have hsum := hbound f (hF hf) n E (fun _ => innerBox_patch _ hw _) hdiag hoff
  have hvol : ∀ i, volume (E i) = ENNReal.ofReal ((w/2)^p) := fun _ => innerBox_volume _ hw _
  simp only [hvol, Finset.sum_const, Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hv' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ (w/2)^p),
    ENNReal.toReal_ofReal ha] at hv'
  exact (not_lt_of_ge hv') ((div_lt_iff₀ (by positivity : 0 < (w/2)^p)).mp hn)

end HalfBall
