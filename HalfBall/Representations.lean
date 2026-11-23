module

public import HalfBall.Scales

@[expose] public section
namespace HalfBall

open Filter Finset
open scoped Topology Pointwise
variable {p : ℕ}

theorem packing_union_le {ι : Type*} [DecidableEq ι] (I : Finset ι) (Y : ι → Finset (V p)) :
    (packing (I.biUnion Y)).card ≤ ∑ i ∈ I, (packing (Y i)).card := by
  classical
  let P := packing (I.biUnion Y)
  obtain ⟨hsub,hsep,_⟩ := packing_spec (I.biUnion Y)
  have hcov : P ⊆ I.biUnion (fun i => P ∩ Y i) := by
    intro x hx
    obtain ⟨i,hi,hx'⟩ := mem_biUnion.mp (hsub hx)
    exact mem_biUnion.mpr ⟨i,hi,mem_inter.mpr ⟨hx,hx'⟩⟩
  refine (card_le_card hcov).trans (card_biUnion_le.trans (sum_le_sum fun i _ =>
    (packing_spec _).2.2 _ inter_subset_right ?_))
  intro x hx y hy
  exact hsep x (mem_inter.mp hx).1 y (mem_inter.mp hy).1

/-- A finite family of strictly positive limiting fractions has one positive
lower threshold. The auxiliary value one also covers an empty label set. -/
private theorem common_fraction {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ < a i := by
  classical
  let D := insert 1 (univ.image (fun i => a i / 2))
  have hD : D.Nonempty := insert_nonempty ..
  refine ⟨D.min' hD,?_,fun i => (min'_le D _ (mem_insert_of_mem (mem_image_of_mem _ (mem_univ i)))).trans_lt
    (half_lt_self (ha i))⟩
  rcases mem_insert.mp (min'_mem D hD) with h | h
  · rw [h]; norm_num
  · obtain ⟨i,_,h⟩ := mem_image.mp h
    rw [← h]; exact half_pos (ha i)

/-- Lemma A.5 from A.4, with one common subsequence for every anchor.
Low-packing labels have vanishing total packing fraction. The low-energy
remainder is kept inside the part to which the exact-triple bound applies. -/
theorem representations_of_anchored_triangles {B : Set (V p)} (hp : 0 < p)
    (hB : LocallyFiniteSites B) {η : V p} {S : ℕ → ℝ} (hS : HalfBallCount B η S)
    (hA4 : AnchoredTriangleBound hB η S) : HasRepresentations B η S := by
  classical
  obtain ⟨τ,hτ,htri⟩ := hA4
  obtain ⟨C,hC,hsize⟩ := scale_count_bound hB hp hS
  obtain ⟨j₀,hj₀⟩ := eventually_atTop.mp hsize
  let r (n : ℕ) := S (n+j₀)
  let N (n : ℕ) := scaleVolume p (r n)
  let X (n : ℕ) := sites hB η (r n)
  have hN (n) : 0 < N n := by unfold N scaleVolume r; positivity [hS.1 (n+j₀)]
  have hX (n) : ((X n).card : ℝ) ≤ C*N n := hj₀ (n+j₀) (by omega)
  let ε := (τ/48)^4 / (C^5+1)
  obtain ⟨K,L,hK,hdec⟩ := padded_decomposition (p := p) C ε hC (by dsimp [ε]; positivity)
  choose U Y he hsub hcover hdis hdiff using fun n => hdec (N n) (X n) (hN n) (hX n)
  have hY (n i) : ((Y n i).card : ℝ) ≤ C * N n := by
    exact (by exact_mod_cast card_le_card (hsub n i) : ((Y n i).card : ℝ) ≤ (X n).card).trans (hX n)
  obtain ⟨φ,a,hφ,ha,hlim⟩ := packing_subsequence Y N C hN hY
  let ψ (n : ℕ) := φ n + j₀
  have hψ : StrictMono ψ := fun i j hij => Nat.add_lt_add_right (hφ hij) _
  let D := univ.filter (fun i : Fin L => a i = 0)
  let Z (n : ℕ) := D.biUnion (Y (φ n))
  have hzsub n : Z n ⊆ X (φ n) := biUnion_subset.mpr (fun i _ => hsub _ i)
  have hzero : Tendsto (fun n => ((packing (Z n)).card : ℝ)/N (φ n)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => ∑ i ∈ D, ((packing (Y (φ n) i)).card : ℝ)/N (φ n)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum D (fun i hi => (mem_filter.mp hi).2 ▸ hlim i :
        ∀ i ∈ D, Tendsto (fun n => ((packing (Y (φ n) i)).card : ℝ)/N (φ n)) atTop (𝓝 0))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    · intro n; positivity [hN (φ n)]
    · intro n
      dsimp only
      rw [← sum_div, ← Nat.cast_sum]
      apply div_le_div_of_nonneg_right _ (hN _).le
      exact_mod_cast packing_union_le D (Y (φ n))
  let I := {i : Fin L // 0 < a i}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let W n (i : Fin (Fintype.card I)) := Y (φ n) (e i).val
  obtain ⟨δ,hδ,hδi⟩ := common_fraction (fun i : I => a i.val) Subtype.property
  let β := τ/(16*((Fintype.card I : ℝ)^3+1))
  refine ⟨ψ,Fintype.card I,W,K,C,δ,β,hψ,hK,hC.le,hδ,by dsimp [β]; positivity,?_,?_,?_,?_⟩
  · exact Eventually.of_forall fun n i _ hx => (mem_sites ..).mp (hsub (φ n) (e i).val hx)
  · exact Eventually.of_forall fun n _ _ hij =>
      hdis _ (fun h => hij (e.injective (Subtype.ext h)))
  · apply eventually_all.mpr
    intro i
    filter_upwards [(hlim (e i).val).eventually_const_lt (hδi (e i))] with n hn
    refine ⟨hY _ _,hdiff _ _,packing _,(packing_spec _).1,?_,(packing_spec _).2.1⟩
    exact ((lt_div_iff₀ (hN (φ n))).mp hn).le
  · intro s hs
    filter_upwards [htri ψ hψ Z hzsub hzero s hs] with n hn
    let X₁ := X (φ n) \ Z n
    have hX₁ : (X₁.card : ℝ) ≤ C * N (φ n) :=
      (by exact_mod_cast card_le_card (sdiff_subset (s := X (φ n)) (t := Z n)) :
        (X₁.card : ℝ) ≤ (X (φ n)).card).trans (hX _)
    apply force_tuple (W n) _ X₁ (U (φ n)) s hC.le (hN _) hτ hX₁ (he _).le _ _ hn
    · intro x hx
      obtain ⟨hxX,hxZ⟩ := mem_sdiff.mp hx
      rcases hcover _ x hxX with hu | ⟨i,hi⟩
      · exact Or.inl hu
      have hpos : 0 < a i := lt_of_le_of_ne (ha i).1 (fun h =>
        hxZ (mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,h.symm⟩,hi⟩))
      exact Or.inr ⟨e.symm ⟨i,hpos⟩,by simpa [W] using hi⟩
    · exact anchoredOffsets_subset _ _ _ _

/-- A.4 is the sole additional mathematical hypothesis in this reduction of A.3. -/
theorem geometric_local_count_of_anchored_triangles {B : Set (V p)} (hp : 0 < p)
    (hB : LocallyFiniteSites B) {η : V p} {S : ℕ → ℝ} (hS : HalfBallCount B η S)
    (hA4 : AnchoredTriangleBound hB η S) : ∃ M, BallCap (B ∩ halfSpace η) M :=
  geometric_local_count_of_representations hp hS.1 (representations_of_anchored_triangles hp hB hS hA4)

end HalfBall
