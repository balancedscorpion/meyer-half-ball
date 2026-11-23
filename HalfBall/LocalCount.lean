module

public import HalfBall.Packing
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Filter Finset
open scoped Pointwise
variable {p : ℕ}

noncomputable def signed (b : Bool) (Y : Finset (V p)) : Finset (V p) :=
  if b then -Y else Y

def signValue (b : Bool) : ℝ := if b then -1 else 1

/-- A common scale, the lower representation threshold, and the size and
packing estimates for the signed pieces appearing at that scale. -/
structure PieceBounds (Y : Finset (V p)) (N K C δ : ℝ) : Prop where
  size : (Y.card : ℝ) ≤ C * N
  diff : ((Y - Y).card : ℝ) ≤ K * Y.card
  packing : ∃ P ⊆ Y, δ * N ≤ (P.card : ℝ) ∧ ∀ q ∈ P, ∀ r ∈ P, q ≠ r → 1 < dist q r

theorem PieceBounds.signed {Y : Finset (V p)} {N K C δ : ℝ}
    (h : PieceBounds Y N K C δ) (b : Bool) : PieceBounds (signed b Y) N K C δ := by
  classical
  cases b
  · exact h
  · obtain ⟨hs,hd,P,hP,hcard,hsep⟩ := h
    change PieceBounds (-Y) N K C δ
    refine ⟨by simpa, ?_, -P, ?_, by simpa using hcard, ?_⟩
    · simpa [sub_eq_add_neg, add_comm] using hd
    · intro q hq
      simpa using hP (show -q ∈ P by simpa using hq)
    · intro q hq r hr hne
      simpa using hsep (-q) (by simpa using hq) (-r) (by simpa using hr) (by simpa)

abbrev Label (L : ℕ) := Fin L × Bool
abbrev Tuple (L : ℕ) := Label L × Label L × Label L

def multiplier {L} (u : Tuple L) :=
  signValue u.1.2 + signValue u.2.1.2 + signValue u.2.2.2

theorem multiplier_bounds {L} (u : Tuple L) :
    multiplier u ≠ 0 ∧ |multiplier u| ≤ 3 := by
  rcases u with ⟨⟨i,b⟩,⟨j,c⟩,⟨k,d⟩⟩
  cases b <;> cases c <;> cases d <;> norm_num [multiplier, signValue]

def qualifies {L} (Y : Fin L → Finset (V p)) (N β : ℝ) (u : Tuple L) (s : V p) : Prop :=
  β * N ^ 2 ≤ ((representations (signed u.1.2 (Y u.1.1)) (signed u.2.1.2 (Y u.2.1.1))
    (signed u.2.2.2 (Y u.2.2.1)) (multiplier u • s)).card : ℝ)

/-- For one tuple and a small ball the bound is independent of the scale. -/
theorem tuple_cap {L} {Y : Fin L → Finset (V p)} {N K C δ β : ℝ}
    (hN : 0 < N) (hK : 0 ≤ K) (hC : 0 ≤ C) (hδ : 0 < δ) (hβ : 0 < β)
    (hY : ∀ i, PieceBounds (Y i) N K C δ) (u : Tuple L) (y : V p) (T : Finset (V p))
    (hT : ∀ s ∈ T, s ∈ Metric.ball y (1 / 7) ∧ qualifies Y N β u s) :
    (T.card : ℝ) ≤ K * C ^ 3 / (δ * β) := by
  classical
  let A := signed u.1.2 (Y u.1.1)
  let B := signed u.2.1.2 (Y u.2.1.1)
  let D := signed u.2.2.2 (Y u.2.2.1)
  have ha : PieceBounds A N K C δ := (hY _).signed _
  have hb : PieceBounds B N K C δ := (hY _).signed _
  have hd : PieceBounds D N K C δ := (hY _).signed _
  obtain ⟨P,hP,hcard,hsep⟩ := ha.packing
  obtain ⟨hm,hm3⟩ := multiplier_bounds u
  have hdiam (s) (hs : s ∈ T) (t) (ht : t ∈ T) : ‖multiplier u • (s-t)‖ ≤ 1 := by
    have hst := dist_triangle_right s t y
    have hs' := Metric.mem_ball.mp (hT s hs).1
    have ht' := Metric.mem_ball.mp (hT t ht).1
    rw [norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
    calc |multiplier u| * dist s t ≤ 3 * dist s t := by gcongr
         _ ≤ 1 := by linarith
  have hcount := packing_incidence A B D P T _ hm hP hsep hdiam
  have hreal : (∑ s ∈ T, (P.card : ℝ) * (representations A B D (multiplier u • s)).card) ≤
      ((A - A).card : ℝ) * (B.card * D.card) := by exact_mod_cast hcount
  have hbound : T.card * (δ * N * (β * N ^ 2)) ≤ K * C ^ 3 * N ^ 3 := calc
    _ = ∑ _s ∈ T, δ * N * (β * N ^ 2) := by simp
    _ ≤ _ := Finset.sum_le_sum fun s hs => mul_le_mul hcard (hT s hs).2
      (by positivity) (by positivity)
    _ ≤ _ := hreal
    _ ≤ K * (C * N) * (C * N * (C * N)) := by
      gcongr
      · exact ha.diff.trans (mul_le_mul_of_nonneg_left ha.size hK)
      · exact hb.size
      · exact hd.size
    _ = _ := by ring
  apply (le_div_iff₀ (mul_pos hδ hβ)).mpr
  apply le_of_mul_le_mul_right (a := N ^ 3) _ (by positivity)
  convert hbound using 1
  ring

/-- A.6 summed over the finite list of tuples and a cover of the unit ball. -/
theorem represented_ball_cap (p L : ℕ) (K C δ β : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hβ : 0 < β) :
    ∃ M : ℕ, ∀ (Y : Fin L → Finset (V p)) (N : ℝ), 0 < N →
      (∀ i, PieceBounds (Y i) N K C δ) → BallCap {s | ∃ u, qualifies Y N β u s} M := by
  classical
  obtain ⟨F,hF⟩ := small_ball_cover p
  let pairs := F ×ˢ (univ : Finset (Tuple L))
  let H := ⌈K * C ^ 3 / (δ * β)⌉₊
  refine ⟨pairs.card * H, ?_⟩
  intro Y N hN hY y T hT
  let part (a : V p × Tuple L) := T.filter fun s =>
    s ∈ Metric.ball (y+a.1) (1/7) ∧ qualifies Y N β a.2 s
  have hsub : T ⊆ pairs.biUnion part := by
    intro s hs
    obtain ⟨⟨u,hu⟩,hsy⟩ := hT hs
    obtain ⟨c,hc,hsc⟩ := Set.mem_iUnion₂.mp (hF y hsy)
    exact mem_biUnion.mpr ⟨(c,u),mem_product.mpr ⟨hc,mem_univ _⟩,mem_filter.mpr ⟨hs,hsc,hu⟩⟩
  calc T.card ≤ _ := card_le_card hsub
       _ ≤ _ := card_biUnion_le
       _ ≤ ∑ _a ∈ pairs, H := by
         apply sum_le_sum
         intro a _
         have h := tuple_cap hN hK hC hδ hβ hY a.2 (y+a.1) (part a)
           (fun s hs => (mem_filter.mp hs).2)
         exact_mod_cast h.trans (Nat.le_ceil _)
       _ = _ := by simp

/-- Each anchor has its own threshold on a single sequence of predicates. -/
theorem cap_of_eventually_qualifying {E : Set (V p)} {Q : ℕ → Set (V p)} {M : ℕ}
    (hs : ∀ s ∈ E, ∀ᶠ j in atTop, s ∈ Q j) (hc : ∀ᶠ j in atTop, BallCap (Q j) M) :
    BallCap E M := by
  intro y T hT
  have hall : ∀ᶠ j in atTop, ∀ s ∈ T, s ∈ Q j :=
    (Filter.eventually_all_finset _).mpr fun s hs' => hs s (hT hs').1
  obtain ⟨j,hj,hcap⟩ := (hall.and hc).exists
  exact hcap y T fun s hs' => ⟨hj s hs', (hT hs').2⟩

end HalfBall
