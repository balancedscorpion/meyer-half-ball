module

public import HalfBall.Subsequence
public import HalfBall.Forcing

@[expose] public section
namespace HalfBall

open Finset Filter
open scoped Pointwise Topology InnerProductSpace
variable {p : ℕ}

/-- The measured finite set at one radius, including both boundary faces. -/
noncomputable def sites {B : Set (V p)} (hB : LocallyFiniteSites B) (η : V p) (R : ℝ) :
    Finset (V p) :=
  ((hB _ (isCompact_closedBall 0 R)).subset
    (show B ∩ halfBall η R ⊆ B ∩ Metric.closedBall 0 R from fun _ h => ⟨h.1,h.2.2⟩)).toFinset

@[simp] theorem mem_sites {B : Set (V p)} (hB : LocallyFiniteSites B) (η : V p) (R : ℝ) (s) :
    s ∈ sites hB η R ↔ s ∈ B ∩ halfBall η R := Set.Finite.mem_toFinset _

theorem scale_count_bound {B : Set (V p)} (hB : LocallyFiniteSites B) {η : V p}
    (hp : 0 < p) {S : ℕ → ℝ} (hS : HalfBallCount B η S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ((sites hB η (S n)).card : ℝ) ≤ C * scaleVolume p (S n) := by
  obtain ⟨hpos,_,k,hk,he⟩ := hS
  let d : ℝ := 3 * Real.sqrt p
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨(k+1)*d^p,by positivity,?_⟩
  filter_upwards [he] with n hn
  have hc : (sites hB η (S n)).card = (B ∩ halfBall η (S n)).ncard := by
    exact (Set.ncard_eq_toFinset_card _ _).symm
  rw [hc]
  calc _ ≤ _ := hn
       _ ≤ (k+1)*S n^p := by apply mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (hpos n).le p)
       _ = _ := by change _ = (k+1)*d^p * (S n/d)^p; rw [div_pow]; field_simp

def cube (p : ℕ) (R : ℝ) : Set (V p) :=
  {x | ∀ k, |x k| ≤ R / (6 * Real.sqrt p)}

/-- The two signs of every eligible displacement, with actual duplicate
offsets erased. The height restriction is imposed on the displacement. -/
noncomputable def anchoredOffsets (X : Finset (V p)) (s η : V p) (R : ℝ) : Finset (V p) := by
  classical
  let W := X.filter fun x => x ≠ s ∧ 0 ≤ ⟪η, x-s⟫_ℝ ∧ x-s ∈ cube p R - cube p R
  exact offsets s false W ∪ offsets s true W

theorem anchoredOffsets_subset (X : Finset (V p)) (s η : V p) (R : ℝ) :
    ∀ x ∈ anchoredOffsets X s η R, ∃ b, x ∈ offsets s b X := by
  classical
  intro x hx
  rcases mem_union.mp hx with h | h
  · obtain ⟨z,hz,rfl⟩ := mem_image.mp h
    exact ⟨false,mem_image_of_mem _ (mem_filter.mp hz).1⟩
  · obtain ⟨z,hz,rfl⟩ := mem_image.mp h
    exact ⟨true,mem_image_of_mem _ (mem_neg'.mpr (mem_filter.mp (mem_neg'.mp hz)).1)⟩

/-- The partition-uniform conclusion of A.4. The same positive τ works
after passing to any subsequence; each anchor has its own eventuality. -/
def AnchoredTriangleBound {B : Set (V p)} (hB : LocallyFiniteSites B) (η : V p) (S : ℕ → ℝ) :
    Prop :=
  ∃ τ : ℝ, 0 < τ ∧ ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (X₀ : ℕ → Finset (V p)),
    (∀ n, X₀ n ⊆ sites hB η (S (φ n))) →
    Tendsto (fun n => ((packing (X₀ n)).card : ℝ) / scaleVolume p (S (φ n))) atTop (𝓝 0) →
    ∀ s ∈ B ∩ halfSpace η, ∀ᶠ n in atTop,
      let F := anchoredOffsets (sites hB η (S (φ n)) \ X₀ n) s η (S (φ n))
      τ * scaleVolume p (S (φ n))^2 < ((triples F F F 0).card : ℝ)

/-- Indexed, padded form of the low-energy decomposition. Empty padding
keeps the label set identical across scales before taking limits. -/
theorem padded_decomposition (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ (K : ℝ) (L : ℕ), 0 ≤ K ∧ ∀ (N : ℝ) (X : Finset (V p)), 0 < N → (X.card : ℝ) ≤ C*N →
    ∃ (U : Finset (V p)) (Y : Fin L → Finset (V p)), (addEnergy U U : ℝ) < ε*N^3 ∧
      (∀ i, Y i ⊆ X) ∧ (∀ x ∈ X, x ∈ U ∨ ∃ i, x ∈ Y i) ∧
      (Pairwise fun i j => Disjoint (Y i) (Y j)) ∧
      ∀ i, ((Y i - Y i).card : ℝ) ≤ K*(Y i).card := by
  classical
  obtain ⟨c,K,L,_,hK,he⟩ := energy_decomposition (G := V p) C ε hC hε
  refine ⟨K,L,hK,?_⟩
  intro N X hN hX
  obtain ⟨U,ys,hu,hp,_,hE,hy,hl⟩ := he N X hN hX
  let Y (i : Fin L) := if h : i.val < ys.length then ys[i.val] else ∅
  have fold_mem (ls : List (Finset (V p))) (x : V p) :
      x ∈ ls.foldr (· ∪ ·) ∅ ↔ ∃ A ∈ ls, x ∈ A := by induction ls <;> simp_all
  refine ⟨U,Y,hE,?_,?_,?_,?_⟩
  · intro i x hx
    rw [← hu,mem_union]
    right
    apply (fold_mem _ _).mpr
    by_cases hi : i.val < ys.length
    · exact ⟨ys[i.val],List.getElem_mem _, by simpa [Y,hi] using hx⟩
    · simp [Y,hi] at hx
  · intro x hx
    rw [← hu,mem_union,fold_mem] at hx
    rcases hx with h | ⟨A,ha,hx⟩
    · exact Or.inl h
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ha
    exact Or.inr ⟨⟨i,hi.trans_le hl⟩,by simpa [Y,hi] using hx⟩
  · intro i j hij
    by_cases hi : i.val < ys.length <;> by_cases hj : j.val < ys.length
    · simp only [Y,hi,hj,dite_eq_left]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact List.pairwise_iff_getElem.mp hp _ _ hi hj h
      · exact (List.pairwise_iff_getElem.mp hp _ _ hj hi h).symm
    all_goals simp [Y,hi,hj]
  · intro i
    by_cases hi : i.val < ys.length
    · simpa [Y,hi] using (hy ys[i.val] (List.getElem_mem _)).2
    · simp [Y,hi]

end HalfBall
