module

public import HalfBall.Geometry.Mesh
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Finset
open scoped InnerProductSpace Pointwise
variable {p m : ℕ}

theorem mem_anchoredOffsets {X : Finset (V p)} {s η h : V p} {R : ℝ} :
    h ∈ anchoredOffsets X s η R ↔
      ∃ x ∈ X, x ≠ s ∧ 0 ≤ ⟪η,x-s⟫_ℝ ∧ x-s ∈ cube p R - cube p R ∧
        (h = x-s ∨ h = -(x-s)) := by
  classical
  simp only [anchoredOffsets,offsets,signed,shift,signValue,Bool.false_eq_true,ite_false,
    ite_true,neg_one_smul,one_smul,mem_union,mem_image,mem_filter,mem_neg']
  constructor
  · rintro (⟨x,⟨hx,hne,hη,hc⟩,rfl⟩ | ⟨z,⟨hz,hne,hη,hc⟩,rfl⟩)
    · exact ⟨x,hx,hne,hη,hc,Or.inl rfl⟩
    · exact ⟨-z,hz,hne,hη,hc,Or.inr (by abel)⟩
  · rintro ⟨x,hx,hne,hη,hc,h|h⟩
    · exact Or.inl ⟨x,⟨hx,hne,hη,hc⟩,h.symm⟩
    · exact Or.inr ⟨-x,by simpa using And.intro hx (And.intro hne (And.intro hη hc)),by rw [h]; abel⟩

theorem anchored_symmetric (X : Finset (V p)) (s η : V p) (R : ℝ) :
    ∀ h ∈ anchoredOffsets X s η R, -h ∈ anchoredOffsets X s η R := by
  intro h hh
  obtain ⟨x,hx,hne,hη,hc,hs⟩ := mem_anchoredOffsets.mp hh
  exact mem_anchoredOffsets.mpr ⟨x,hx,hne,hη,hc,by rcases hs with rfl|rfl <;> simp⟩

theorem anchored_card (X : Finset (V p)) (s η : V p) (R : ℝ) :
    (anchoredOffsets X s η R).card ≤ 2*X.card := by
  classical
  let W := X.filter fun x => x ≠ s ∧ 0 ≤ ⟪η,x-s⟫_ℝ ∧ x-s ∈ cube p R - cube p R
  have h (b) : (offsets s b W).card ≤ X.card :=
    card_image_le.trans ((signed_card b W) ▸ card_filter_le _ _)
  exact (card_union_le ..).trans (by linarith [h true,h false] :
    (offsets s false W).card + (offsets s true W).card ≤ 2*X.card)

theorem packing_covers (X : Finset (V p)) {x : V p} (hx : x ∈ X) :
    ∃ y ∈ packing X, dist x y ≤ 1 := by
  classical
  obtain ⟨hsub,hsep,hmax⟩ := packing_spec X
  by_contra! h
  have hnot : x ∉ packing X := fun hmem => by have hh := h x hmem; rw [dist_self] at hh; linarith
  have hnew : UnitSeparated (insert x (packing X)) := by
    intro u hu v hv hne
    rcases mem_insert.mp hu with hu|hu <;> rcases mem_insert.mp hv with hv|hv
    · exact False.elim (hne (hu.trans hv.symm))
    · exact hu ▸ h v hv
    · rw [hv,dist_comm]; exact h u hu
    · exact hsep u hu v hv hne
  have hle := hmax _ (insert_subset hx hsub) hnew
  rw [card_insert_of_notMem hnot] at hle
  omega

/-- A positive threshold below all nonzero values on a finite set, also for
an empty list of nonzero values. -/
theorem finite_gap {α : Type*} (F : Finset α) (f : α → ℝ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ x ∈ F, f x ≠ 0 → d ≤ |f x| := by
  classical
  let D := insert 1 ((F.filter (fun x => f x ≠ 0)).image (fun x => |f x|))
  have hD : D.Nonempty := insert_nonempty ..
  refine ⟨D.min' hD,?_,min'_le _ _ (mem_insert_self ..),?_⟩
  · rcases mem_insert.mp (min'_mem D hD) with h|h
    · rw [h]; norm_num
    · obtain ⟨x,hx,h⟩ := mem_image.mp h
      rw [← h]; exact abs_pos.mpr (mem_filter.mp hx).2
  · intro x hx hn
    exact min'_le _ _ (mem_insert_of_mem (mem_image_of_mem _ (mem_filter.mpr ⟨hx,hn⟩)))

theorem anchor_isolation {B : Set (V p)} (hB : LocallyFiniteSites B) (s : V p) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ x ∈ B, x ≠ s → d ≤ ‖x-s‖ := by
  let L := (hB _ (isCompact_closedBall s 1)).toFinset
  obtain ⟨d,hd,hd1,hmin⟩ := finite_gap L (fun x => ‖x-s‖)
  refine ⟨d,hd,hd1,?_⟩
  intro x hx hne
  by_cases h : ‖x-s‖ ≤ 1
  · have hm : x ∈ L := (Set.Finite.mem_toFinset _).mpr ⟨hx,by simpa [Metric.mem_closedBall,dist_eq_norm] using h⟩
    simpa using hmin x hm (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
  · exact hd1.trans (le_of_not_ge h)

noncomputable def coarsePartners (m : ℕ) (d : ℝ) (F : Finset (V p)) (v : Grid p m) :=
  F.biUnion fun h => nearGrid m d (corner d v+h) (2*d)

theorem coarse_no_self {d : ℝ} (hd : 0 < d) (F : Finset (V p))
    (hsep : ∀ h ∈ F, Real.sqrt p*(2*d) < ‖h‖) (v : Grid p m) :
    v ∉ coarsePartners m d F v := by
  intro hv
  obtain ⟨h,hh,hn⟩ := mem_biUnion.mp hv
  apply (not_lt_of_ge (norm_le_of_coords h (by positivity) ?_)) (hsep _ hh)
  intro i
  have hi := (mem_nearGrid ..).mp hn i
  change |corner d v i - (corner d v i + h i)| ≤ 2*d at hi
  simpa using hi

theorem coarse_partner_bound (m : ℕ) {d : ℝ} (hd : 0 < d) (X : Finset (V p))
    (s η : V p) (R : ℝ) (v : Grid p m) :
    (coarsePartners m d (anchoredOffsets X s η R) v).card ≤
      (packing X).card * (2 * (2 * ⌈(2*d+1)/d⌉₊ + 2)^p) := by
  classical
  let b := ⌈(2*d+1)/d⌉₊
  let window (z : V p) := nearGrid m d (corner d v + z) (2*d+1)
  let part (y : V p) := window (y-s) ∪ window (-(y-s))
  have hw z : (window z).card ≤ (2*b+2)^p := card_nearGrid m b hd
    ((div_le_iff₀ hd).mp (Nat.le_ceil _)) _
  have hs : coarsePartners m d (anchoredOffsets X s η R) v ⊆ (packing X).biUnion part := by
    intro w hmem
    obtain ⟨h,hh,hn⟩ := mem_biUnion.mp hmem
    obtain ⟨x,hx,_,_,_,hs⟩ := mem_anchoredOffsets.mp hh
    obtain ⟨y,hy,hxy⟩ := packing_covers X hx
    apply mem_biUnion.mpr; refine ⟨y,hy,?_⟩
    rcases hs with rfl|rfl
    case' inl => apply mem_union_left
    case' inr => apply mem_union_right
    all_goals
      apply (mem_nearGrid ..).mpr
      intro i
      have hc := abs_le.mp ((mem_nearGrid ..).mp hn i)
      have hdist := abs_le.mp ((coord_le_norm (x-y) i).trans (dist_eq_norm x y ▸ hxy))
      simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.neg_apply] at hc hdist ⊢
      apply abs_le.mpr
      constructor <;> linarith
  exact (card_le_card hs).trans (card_biUnion_le.trans ((sum_le_sum (fun y _ =>
    (card_union_le ..).trans (by linarith [hw (y-s),hw (-(y-s))] :
      (window (y-s)).card + (window (-(y-s))).card ≤ 2*(2*b+2)^p))).trans (by simp [b])))

end HalfBall
