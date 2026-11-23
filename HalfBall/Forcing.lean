module

public import HalfBall.Triples

@[expose] public section
namespace HalfBall

open Finset
variable {p : ℕ}

private theorem mem_offset_parts {s : V p} {b} {U X : Finset (V p)} {L} {Y : Fin L → Finset (V p)}
    (hc : ∀ x ∈ X, x ∈ U ∨ ∃ i, x ∈ Y i) {v} (hv : v ∈ offsets s b X) :
    v ∈ offsets s b U ∨ ∃ i, v ∈ offsets s b (Y i) := by
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
  suffices z ∈ signed b U ∨ ∃ i, z ∈ signed b (Y i) by
    rcases this with h | ⟨i,h⟩
    · exact Or.inl (mem_image_of_mem _ h)
    · exact Or.inr ⟨i,mem_image_of_mem _ h⟩
  cases b
  · exact hc z hz
  · rcases hc (-z) (mem_neg'.mp hz) with h | ⟨i,h⟩
    · exact Or.inl (mem_neg'.mpr h)
    · exact Or.inr ⟨i,mem_neg'.mpr h⟩

/-- Each sign pattern costs at most three remainder terms, regardless of the
number of structured labels. -/
theorem split_triples {L : ℕ} (Y : Fin L → Finset (V p)) (U X : Finset (V p))
    (cover : ∀ x ∈ X, x ∈ U ∨ ∃ i, x ∈ Y i) (s : V p) (a b c : Bool) :
    (triples (offsets s a X) (offsets s b X) (offsets s c X) 0).card ≤
      (triples (offsets s a U) (offsets s b X) (offsets s c X) 0).card +
      (triples (offsets s a X) (offsets s b U) (offsets s c X) 0).card +
      (triples (offsets s a X) (offsets s b X) (offsets s c U) 0).card +
      ∑ i : Fin L × Fin L × Fin L, (triples (offsets s a (Y i.1))
        (offsets s b (Y i.2.1)) (offsets s c (Y i.2.2)) 0).card := by
  classical
  let tr A B C := triples (offsets s a A) (offsets s b B) (offsets s c C) 0
  let part (i : Fin L × Fin L × Fin L) := tr (Y i.1) (Y i.2.1) (Y i.2.2)
  have hsub : tr X X X ⊆ tr U X X ∪ tr X U X ∪ tr X X U ∪ univ.biUnion part := by
    rintro ⟨x,y,z⟩ h
    obtain ⟨hm,he⟩ := mem_filter.mp h
    obtain ⟨hx,hyz⟩ := mem_product.mp hm
    obtain ⟨hy,hz⟩ := mem_product.mp hyz
    simp only [mem_union, mem_biUnion, mem_univ, true_and]
    rcases mem_offset_parts cover hx with h | ⟨i,hi⟩
    · exact Or.inl (Or.inl (Or.inl (mem_filter.mpr ⟨mem_product.mpr ⟨h,hyz⟩,he⟩)))
    rcases mem_offset_parts cover hy with h | ⟨j,hj⟩
    · exact Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨mem_product.mpr ⟨hx,mem_product.mpr ⟨h,hz⟩⟩,he⟩)))
    rcases mem_offset_parts cover hz with h | ⟨k,hk⟩
    · exact Or.inl (Or.inr (mem_filter.mpr ⟨mem_product.mpr ⟨hx,mem_product.mpr ⟨hy,h⟩⟩,he⟩))
    exact Or.inr ⟨(i,j,k),mem_filter.mpr ⟨mem_product.mpr ⟨hi,mem_product.mpr ⟨hj,hk⟩⟩,he⟩⟩
  exact (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add
    ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _)) card_biUnion_le))

theorem bad_middle {C N γ : ℝ} (hC : 0 ≤ C) (hN : 0 < N) (hγ : 0 < γ)
    (X U : Finset (V p)) (hX : (X.card : ℝ) ≤ C*N)
    (hU : (addEnergy U U : ℝ) ≤ γ^4 / (C^5+1) * N^3) (a b c : Bool) (t : V p) :
    ((triples (signed a X) (signed b U) (signed c X) t).card : ℝ) ≤ γ * N^2 := by
  rw [card_triples]
  have h := reps_fourth (signed a X) (signed b U) (signed c X) t X.card
    (by simp [signed_card]) (by simp [signed_card])
  rw [energy_signed] at h
  have h' : ((representations (signed a X) (signed b U) (signed c X) t).card : ℝ)^4 ≤
      (X.card : ℝ)^5 * addEnergy U U := by exact_mod_cast h
  apply le_of_pow_le_pow_left₀ (n := 4) (by decide) (by positivity)
  calc _ ≤ _ := h'
       _ ≤ (C*N)^5 * (γ^4 / (C^5+1) * N^3) := by gcongr
       _ ≤ (γ*N^2)^4 := by
         field_simp
         nlinarith [show 0 ≤ γ^4*N^8 by positivity]

/-- Among the eight sign patterns choose the one covering most of the actual
zero-sum offset triples. An offset with two possible signs may be counted twice. -/
theorem sign_pigeonhole (F X : Finset (V p)) (s : V p)
    (hf : ∀ x ∈ F, ∃ b, x ∈ offsets s b X) :
    ∃ a b c, (triples F F F 0).card ≤ 8 *
      (triples (offsets s a X) (offsets s b X) (offsets s c X) 0).card := by
  classical
  let part (i : Bool × Bool × Bool) := triples (offsets s i.1 X) (offsets s i.2.1 X)
    (offsets s i.2.2 X) 0
  have hsub : triples F F F 0 ⊆ univ.biUnion part := by
    rintro ⟨x,y,z⟩ h
    obtain ⟨hm,he⟩ := mem_filter.mp h
    obtain ⟨hx,hyz⟩ := mem_product.mp hm
    obtain ⟨hy,hz⟩ := mem_product.mp hyz
    obtain ⟨a,ha⟩ := hf x hx
    obtain ⟨b,hb⟩ := hf y hy
    obtain ⟨c,hc⟩ := hf z hz
    exact mem_biUnion.mpr ⟨(a,b,c),mem_univ _,mem_filter.mpr ⟨mem_product.mpr ⟨ha,mem_product.mpr ⟨hb,hc⟩⟩,he⟩⟩
  obtain ⟨i,_,hi⟩ := univ.exists_max_image (fun i => (part i).card) univ_nonempty
  refine ⟨i.1,i.2.1,i.2.2, (card_le_card hsub).trans (card_biUnion_le.trans ?_)⟩
  calc _ ≤ ∑ _j : Bool × Bool × Bool, (part i).card := sum_le_sum hi
       _ = _ := by simp [part]

/-- The signed pigeonhole step in A.5. The energy cutoff is fixed using τ and
C alone. The representation threshold may subsequently depend on L. -/
theorem force_tuple {L : ℕ} (Y : Fin L → Finset (V p)) (F X U : Finset (V p))
    (s : V p) {C N τ : ℝ} (hC : 0 ≤ C) (hN : 0 < N) (hτ : 0 < τ)
    (hX : (X.card : ℝ) ≤ C*N)
    (hU : (addEnergy U U : ℝ) ≤ (τ/48)^4 / (C^5+1) * N^3)
    (cover : ∀ x ∈ X, x ∈ U ∨ ∃ i, x ∈ Y i)
    (hf : ∀ x ∈ F, ∃ b, x ∈ offsets s b X)
    (htri : τ * N^2 < ((triples F F F 0).card : ℝ)) :
    ∃ u, qualifies Y N (τ / (16 * ((L : ℝ)^3 + 1))) u s := by
  classical
  obtain ⟨a,b,c,hsign⟩ := sign_pigeonhole F X s hf
  let m := signValue a + signValue b + signValue c
  let t := m • s
  let β := τ / (16 * ((L : ℝ)^3+1))
  let T (A B D : Finset (V p)) := (triples (signed a A) (signed b B) (signed c D) t).card
  have hsign' : τ*N^2 < 8 * (T X X X : ℝ) := by
    rw [translated_triples] at hsign
    exact htri.trans_le (by exact_mod_cast hsign)
  have hbad (a b c : Bool) := bad_middle hC hN (show 0 < τ/48 by positivity) X U hX hU a b c t
  have h1 : (T U X X : ℝ) ≤ τ/48*N^2 := by
    dsimp only [T]; rw [card_triples_swap₁]; exact hbad b a c
  have h2 : (T X U X : ℝ) ≤ τ/48*N^2 := hbad a b c
  have h3 : (T X X U : ℝ) ≤ τ/48*N^2 := by
    dsimp only [T]; rw [card_triples_swap₂]; exact hbad a c b
  have hsplit := split_triples Y U X cover s a b c
  simp_rw [translated_triples] at hsplit
  let good (i : Fin L × Fin L × Fin L) := T (Y i.1) (Y i.2.1) (Y i.2.2)
  have htotal : (T X X X : ℝ) ≤ T U X X + (T X U X : ℝ) + T X X U + ∑ i, (good i : ℝ) := by
    exact_mod_cast hsplit
  by_contra! h
  have hgood (i : Fin L × Fin L × Fin L) : (good i : ℝ) ≤ β * N^2 := by
    have h' := h ((i.1,a),(i.2.1,b),(i.2.2,c))
    dsimp only [good,T]
    rw [card_triples]
    exact le_of_lt (lt_of_not_ge h')
  have hsum := sum_le_sum (s := (univ : Finset (Fin L × Fin L × Fin L))) (fun i _ => hgood i)
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul] at hsum
  have hβ : (L : ℝ)*(L*L) * (β*N^2) ≤ τ/16*N^2 := by
    unfold β; field_simp; nlinarith [mul_nonneg hτ.le (sq_nonneg N)]
  linarith [hsum.trans hβ]

end HalfBall
