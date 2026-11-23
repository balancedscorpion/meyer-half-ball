module
public import HalfBall.Classification.LatticeCover
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall.Weights
open Set Metric Finset Matrix Submodule Filter
open MeyerGeneralProblem.LevOlevskii
open scoped Topology Pointwise

variable {p : ℕ}
abbrev Mat (p : ℕ) := Matrix (Fin p) (Fin p) ℝ
abbrev coset (a : V p) (T : Mat p) := range (latticeSite a T)

theorem finite_coset (a : V p) (T : Mat p) (hT : T.det ≠ 0) : LocallyFiniteSites (coset a T) :=
  locallyFinite_of_lattice_cover (latticeCovered_of_matrixCover ⟨1,le_rfl,fun _ => a,fun _ => T,
    fun _ => hT,fun _ ⟨z,hz⟩ => ⟨0,z,hz.symm⟩⟩)

theorem period_sub {a z h : V p} {T : Mat p} (hz : z ∈ coset a T) (hh : h ∈ matrixLattice T) :
    z-h ∈ coset a T := (mem_latticeCoset_iff ..).mpr (by
  rw [show z-h-a = (z-a)-h by abel]
  exact (matrixLattice T).sub_mem ((mem_latticeCoset_iff ..).mp hz) hh)

/-- Distinct sites from two cosets have uniform separation whenever the
two lattices share a full-rank period lattice. Close sites can be moved
together into a fixed compact ball before their distances are tested. -/
theorem separated_by_common_periods {a b : V p} {T U H : Mat p}
    (hT : T.det ≠ 0) (hU : U.det ≠ 0) (hH : H.det ≠ 0)
    (hHT : matrixLattice H ≤ matrixLattice T) (hHU : matrixLattice H ≤ matrixLattice U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ coset a T, ∀ y ∈ coset b U, x ≠ y → δ ≤ dist x y := by
  obtain ⟨K,hK,hrep⟩ := matrix_fundamental_region H hH
  obtain ⟨R,_,hR⟩ := hK.subset_closedBall_lt 0 0
  let S := (finite_coset a T hT _ (isCompact_closedBall 0 R)).toFinset
  let F := (finite_coset b U hU _ (isCompact_closedBall 0 (R+1))).toFinset
  obtain ⟨δ,hδ,hδ1,hgap⟩ := finite_gap (S ×ˢ F) (fun z => dist z.1 z.2)
  refine ⟨δ,hδ,fun x hx y hy hn => ?_⟩
  by_cases hd : dist x y ≤ 1
  · obtain ⟨h,hh,hxK⟩ := hrep x
    have hxR := hR hxK
    have hd' : dist (x-h) (y-h) = dist x y := dist_sub_right ..
    have hs : x-h ∈ S := (Set.Finite.mem_toFinset _).mpr ⟨period_sub hx (hHT hh),hxR⟩
    have hF : y-h ∈ F := (Set.Finite.mem_toFinset _).mpr ⟨period_sub hy (hHU hh),by
      have := dist_triangle (y-h) (x-h) 0
      rw [dist_comm (y-h) (x-h),hd'] at this
      change dist (y-h) 0 ≤ R+1
      linarith [show dist (x-h) 0 ≤ R from hxR]⟩
    simpa [hd'] using hgap (x-h,y-h) (mem_product.mpr ⟨hs,hF⟩) (show dist (x-h) (y-h) ≠ 0 by rw [hd']; exact dist_ne_zero.mpr hn)
  · exact hδ1.trans (le_of_not_ge hd)

/-- For a pair of lattice cosets the only obstruction to uniform
separation comes from a proper subspace containing their common periods. -/
theorem pair_alternative (a b : V p) (T U : Mat p) (hT : T.det ≠ 0) (hU : U.det ≠ 0) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ coset a T, ∀ y ∈ coset b U, x ≠ y → δ ≤ dist x y) ∨
      ∃ W : Submodule ℝ (V p), W ≠ ⊤ ∧ ∀ x ∈ matrixLattice T, x ∈ matrixLattice U → x ∈ W := by
  let P (i : Bool) := if i then T else U
  have hP i : (P i).det ≠ 0 := by cases i <;> simp [P,hT,hU]
  have h0 i : (0 : V p) ∈ coset 0 (P i) := (mem_latticeCoset_iff ..).mpr (by simp)
  have inter (x : V p) : x ∈ ⋂ i, coset 0 (P i) ↔ x ∈ matrixLattice T ∧ x ∈ matrixLattice U := by
    rw [Set.mem_iInter]
    constructor
    · intro h
      exact ⟨by simpa [P] using (mem_latticeCoset_iff ..).mp (h true),by simpa [P] using (mem_latticeCoset_iff ..).mp (h false)⟩
    · rintro ⟨ht,hu⟩ i
      apply (mem_latticeCoset_iff ..).mpr
      cases i <;> simp [P,ht,hu]
  obtain ⟨H,hH,hs⟩ | ⟨v,hv,hs⟩ := latticeIntersection_lattice_or_hyperplane (fun _ : Bool => 0) P hP 0 h0
  · have hsub {x} (hx : x ∈ matrixLattice H) : x ∈ matrixLattice T ∧ x ∈ matrixLattice U := by
      apply (inter x).mp
      rw [hs,mem_latticeCoset_iff,sub_zero]; exact hx
    exact Or.inl (separated_by_common_periods hT hU hH (fun _ hx => (hsub hx).1) (fun _ hx => (hsub hx).2))
  · let W := LinearMap.ker ((innerSL ℝ v).toLinearMap)
    refine Or.inr ⟨W,fun ht => ?_,fun x hx hy => ?_⟩
    · have h : v ∈ W := ht ▸ mem_top
      exact (real_inner_self_pos.mpr hv).ne' h
    · change inner ℝ v x = 0
      simpa using hs x ((inter x).mpr ⟨hx,hy⟩)

/-- Choose a displacement from each prescribed full-rank lattice so that
every nonempty subset sum misses a fixed finite union of proper flats. -/
theorem avoiding_subset_sums {ι κ : Type*} [Finite κ] [DecidableEq ι]
    (I : Finset ι) (T : ι → Mat p) (hT : ∀ i, (T i).det ≠ 0)
    (W : κ → Submodule ℝ (V p)) (hW : ∀ k, W k ≠ ⊤) (a : κ → V p) :
    ∃ v : ι → V p, (∀ i, v i ∈ matrixLattice (T i)) ∧
      ∀ J ⊆ I, J.Nonempty → ∀ k, (∑ j ∈ J,v j) - a k ∉ W k := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨fun _ => 0,fun i => (matrixLattice _).zero_mem,by simp⟩
  | insert i I hi ih =>
    obtain ⟨u,hu,hs⟩ := ih
    obtain ⟨K,hK,hrep⟩ := matrix_fundamental_region (T i) (hT i)
    obtain ⟨R,_,hR⟩ := hK.subset_closedBall_lt 0 0
    let Z := ↥I.powerset × κ
    let b (z : Z) := a z.2 - ∑ j ∈ z.1.val,u j
    obtain ⟨c,hc⟩ := exists_ball_avoiding_affine_subspaces (fun z : Z => W z.2) (fun z => hW z.2) b R
    obtain ⟨t,ht,hct⟩ := hrep c
    let v := Function.update u i t
    refine ⟨v,fun j => by by_cases h : j = i <;> simp [v,h,ht,hu],fun J hJ hn k => ?_⟩
    by_cases hij : i ∈ J
    · let F := J.erase i
      have hFI : F ⊆ I := fun j hj => (mem_insert.mp (hJ (mem_of_mem_erase hj))).resolve_left (ne_of_mem_erase hj)
      let z : Z := (⟨F,mem_powerset.mpr hFI⟩,k)
      have hdist : dist c t ≤ R := by simpa [dist_eq_norm] using hR hct
      have huJ : ∑ j ∈ F,v j = ∑ j ∈ F,u j := sum_congr rfl (fun j hj => Function.update_of_ne (ne_of_mem_erase hj) ..)
      have he : (∑ j ∈ J,v j)-a k = t-b z := by
        rw [← sum_erase_add _ _ hij]; change (∑ j ∈ F,v j)+v i-a k = _
        rw [huJ,show v i = t from Function.update_self ..]; dsimp [b,z]; abel
      rw [he]; exact fun hh => hdist.not_gt (hc z t hh)
    · have he : ∑ j ∈ J,v j = ∑ j ∈ J,u j := sum_congr rfl (fun j hj =>
        Function.update_of_ne (show j ≠ i from fun h => hij (h ▸ hj)) ..)
      rw [he]
      exact hs J (fun j hj => (mem_insert.mp (hJ hj)).resolve_left (fun h => hij (h ▸ hj))) hn k

end HalfBall.Weights
