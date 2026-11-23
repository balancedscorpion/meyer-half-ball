module

public import HalfBall.Combinatorics.BSG

@[expose] public section
namespace HalfBall

open Finset
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem energy_le_cube (A : Finset G) : addEnergy A A ≤ A.card ^ 3 := by
  rw [Auto.addEnergy_eq_sum_representation_sq]
  calc _ ≤ ∑ s ∈ A + A, A.card * Auto.sumRepresentationCount A s := by
         apply sum_le_sum
         intro s _
         rw [sq]
         gcongr
         exact Auto.sumRepresentationCount_le _ _
       _ = _ := by rw [← mul_sum, Auto.sum_sumRepresentationCount]; ring

/-- At every scale the same constants control all extractions. -/
theorem extract_piece (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ (N : ℝ) (D : Finset G), 0 < N →
      (D.card : ℝ) ≤ C * N → ε * N ^ 3 ≤ addEnergy D D →
      ∃ Y ⊆ D, c * N ≤ (Y.card : ℝ) ∧ ((Y - Y).card : ℝ) ≤ K * Y.card := by
  let H := max 1 (C ^ 3 / ε)
  have hH : 1 ≤ H := le_max_left _ _
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  refine ⟨ε / (C ^ 2 * (80000000000 * H)), 10 ^ 25 * H ^ 10, by positivity, by positivity, ?_⟩
  intro N D hN hsize hE
  have hcub : (addEnergy D D : ℝ) ≤ (D.card : ℝ) ^ 3 := by exact_mod_cast energy_le_cube D
  have hne : D.Nonempty := by
    by_contra! h
    simp [h] at hE
    exact (not_lt_of_ge hE) (by positivity)
  have hscale : (D.card : ℝ) ^ 3 ≤ (C * N) ^ 3 := by gcongr
  have hcoef : C ^ 3 ≤ H * ε := (div_le_iff₀ hε).mp (le_max_right _ _)
  have henergy : (D.card : ℝ) ^ 3 / H ≤ addEnergy D D := by
    apply (div_le_iff₀ hHpos).mpr
    calc _ ≤ (C * N) ^ 3 := hscale
         _ ≤ H * ε * N ^ 3 := by rw [mul_pow]; gcongr
         _ ≤ _ := by rw [mul_assoc, mul_comm H]; gcongr
  obtain ⟨Y,hY,hYsize,hYdiff⟩ := Auto.balog_szemeredi_gowers D hne hH henergy
  refine ⟨Y,hY, ?_,hYdiff⟩
  have hsmall : ε * N ≤ (D.card : ℝ) * C ^ 2 := by
    apply le_of_mul_le_mul_right (a := N ^ 2) _ (by positivity)
    calc _ = ε * N ^ 3 := by ring
         _ ≤ _ := hE.trans hcub
         _ = (D.card : ℝ) * D.card ^ (2 : ℕ) := by ring
         _ ≤ (D.card : ℝ) * (C * N) ^ 2 := by gcongr
         _ = _ := by ring
  apply le_trans _ hYsize
  field_simp
  nlinarith

/-- Repeatedly peel off a structured piece until the remaining energy is small.
The list is disjoint and its length times the common minimum size is
charged to the original cardinality. -/
private theorem peel {N c K ε : ℝ} (hmin : 0 < c * N)
    (extract : ∀ D ⊆ X, ε * N ^ 3 ≤ (addEnergy D D : ℝ) →
      ∃ Y ⊆ D, c * N ≤ (Y.card : ℝ) ∧ ((Y - Y).card : ℝ) ≤ K * Y.card)
    (D : Finset G) (hD : D ⊆ X) :
    ∃ (U : Finset G) (ys : List (Finset G)),
      U ∪ ys.foldr (· ∪ ·) ∅ = D ∧ ys.Pairwise Disjoint ∧ (∀ Y ∈ ys, Disjoint U Y) ∧
      (addEnergy U U : ℝ) < ε * N ^ 3 ∧
      (∀ Y ∈ ys, c * N ≤ (Y.card : ℝ) ∧ ((Y - Y).card : ℝ) ≤ K * Y.card) ∧
      ys.length * (c * N) ≤ (D.card : ℝ) := by
  classical
  by_cases hstop : (addEnergy D D : ℝ) < ε * N ^ 3
  · exact ⟨D, [], by simp, by simp, by simp, hstop, by simp, by simp⟩
  obtain ⟨Y,hY,hcard,hdiff⟩ := extract D hD (le_of_not_gt hstop)
  have hpos : 0 < Y.card := by exact_mod_cast hmin.trans_le hcard
  have hbalance := card_sdiff_add_card_eq_card hY
  have hlt : (D \ Y).card < D.card := by omega
  obtain ⟨U,ys,hu,hpair,hdis,henergy,hpieces,hlen⟩ :=
    peel hmin extract (D \ Y) (sdiff_subset.trans hD)
  have hUY : Disjoint U Y :=
    disjoint_sdiff_self_left.mono_left (hu ▸ subset_union_left (s₂ := ys.foldr (· ∪ ·) ∅))
  have hmem (A) (ha : A ∈ ys) : A ⊆ ys.foldr (· ∪ ·) ∅ := by
    clear hu hpair hdis hpieces hlen
    induction ys with
    | nil => simp at ha
    | cons b bs ih =>
      rcases List.mem_cons.mp ha with rfl | h
      · exact subset_union_left
      · exact (ih (by assumption)).trans subset_union_right
  refine ⟨U, Y :: ys, ?_, List.pairwise_cons.mpr ⟨?_,hpair⟩, ?_,henergy,?_,?_⟩
  · simp only [List.foldr_cons]
    rw [union_left_comm,hu,union_sdiff_of_subset hY]
  · intro A hA
    have hsub : A ⊆ D \ Y := hu ▸ (hmem A hA).trans subset_union_right
    exact (disjoint_sdiff_self_left.mono_left hsub).symm
  · simpa using And.intro hUY hdis
  · simpa using And.intro (And.intro hcard hdiff) hpieces
  · have hsum : ((D \ Y).card : ℝ) + Y.card = D.card := by exact_mod_cast hbalance
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    linarith
termination_by D.card

theorem energy_decomposition (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ (c K : ℝ) (L : ℕ), 0 < c ∧ 0 ≤ K ∧ ∀ (N : ℝ) (X : Finset G), 0 < N →
      (X.card : ℝ) ≤ C*N → ∃ (U : Finset G) (ys : List (Finset G)),
        U ∪ ys.foldr (· ∪ ·) ∅ = X ∧ ys.Pairwise Disjoint ∧ (∀ Y ∈ ys, Disjoint U Y) ∧
        (addEnergy U U : ℝ) < ε * N^3 ∧
        (∀ Y ∈ ys, c*N ≤ (Y.card : ℝ) ∧ ((Y-Y).card : ℝ) ≤ K * Y.card) ∧ ys.length ≤ L := by
  obtain ⟨c,K,hc,hK,he⟩ := extract_piece (G := G) C ε hC hε
  refine ⟨c,K,⌈C/c⌉₊,hc,hK,?_⟩
  intro N X hN hX
  obtain ⟨U,ys,hu,hp,hd,hE,hY,hlen⟩ := peel (mul_pos hc hN)
    (fun D hD => he N D hN ((by exact_mod_cast card_le_card hD : (D.card : ℝ) ≤ X.card).trans hX))
    X Subset.rfl
  refine ⟨U,ys,hu,hp,hd,hE,hY,?_⟩
  have h := hlen.trans hX
  rw [← mul_assoc] at h
  have h' := (le_div_iff₀ hc).mpr ((le_of_mul_le_mul_right h hN))
  exact_mod_cast h'.trans (Nat.le_ceil _)

end HalfBall
