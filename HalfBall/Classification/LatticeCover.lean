/-
Adapted from AppendixA/LaurentReduction.lean in the pinned lev-olevskii-lattice-cover dependency.
See LICENSES/lev-olevskii-lattice-cover-MIT.txt.
-/
module
public import HalfBall.Classification.FilteredDensity
public import HalfBall.LatticeCount
public import HalfBall.Classification.CosetRank
public import AppendixA.UnitDescent
import Mathlib.Tactic
public section
noncomputable section
namespace HalfBall
open MeyerGeneralProblem.LevOlevskii Set Matrix Metric FourierTransform Submodule
open scoped Matrix Classical Pointwise FourierTransform

private def spectralCoordinates {d n : ℕ} (u : Fin n → Space d) :
    Space d →+ (Fin n → Additive Circle) :=
  AddMonoidHom.pi fun i => (frequencyPhase (u i)).toAddMonoidHom

private theorem monomial_on_coordinates {d n : ℕ} (u : Fin n → Space d)
    (m : Fin n → ℤ) (x : Space d) :
    unitaryMonomial m (spectralCoordinates u x) =
      (frequencyPhase (∑ i, m i • u i) x : ℂ) := by
  have symm (y w : Space d) : frequencyPhase y w = frequencyPhase w y := by
    change Real.fourierChar (inner ℝ w y) = Real.fourierChar (inner ℝ y w)
    rw [real_inner_comm]
  rw [symm _ x]
  let f := (frequencyPhase x).toAddMonoidHom
  have h (i) : spectralCoordinates u x i = f (u i) := congrArg Additive.ofMul (symm _ _)
  simp only [unitaryMonomial,h,← map_zsmul,← map_sum]
  rfl

private theorem physical_cosets_of_laurent (hL : UnitaryLaurentCosetTheorem)
    {d n : ℕ} (A : Set (Space d)) (hfg : (AddSubgroup.closure A).FG) (u : Fin n → Space d) :
    ∃ (k : ℕ) (t : Fin k → Space d) (P : Fin k → Submodule ℤ (Space d)),
      (∀ x ∈ A, ∃ j, x-t j ∈ P j) ∧
      ∀ j, CosetSatisfiesRelations A (span ℤ (range u)) (t j) (P j) := by
  let f := spectralCoordinates u
  let Γ := (AddSubgroup.closure A).map f
  have hΓ : Γ.FG := by
    apply (AddSubgroup.fg_iff_addSubmonoid_fg _).mpr
    exact ((AddSubgroup.fg_iff_addSubmonoid_fg _).mp hfg).map f
  obtain ⟨k,s,Q,hcover,hcoset⟩ := hL n Γ hΓ (f '' A) (by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,AddSubgroup.subset_closure hx,rfl⟩)
  choose t _ hts using fun j => (s j).property
  let P (j : Fin k) := ((Q j).comap f).toIntSubmodule
  refine ⟨k,t,P,?_,?_⟩
  · intro x hx
    obtain ⟨j,hj⟩ := hcover _ ⟨x,hx,rfl⟩
    exact ⟨j,show f (x-t j) ∈ Q j by simpa only [map_sub,hts] using hj⟩
  · intro j ι inst c v hv hzero y hy
    choose m hm using fun i => (mem_span_range_iff_exists_fun ℤ).mp (hv i)
    have eval (x : Space d) (i : ι) : unitaryMonomial (m i) (f x) = (frequencyPhase (v i) x : ℂ) := by
      rw [monomial_on_coordinates,hm]
    have htor := hcoset j (f y) hy c m (by
      rintro _ ⟨x,hx,rfl⟩
      simpa only [eval] using hzero x hx)
    have he : (s j).val + f y = f (t j+y) := by rw [map_add,hts]
    simpa only [he,eval] using htor

/-- Proposition B.3, with the finite generation of B.2 as input. The unitary Laurent theorem follows from the pinned unit-equation proof. -/
theorem physical_cover_of_finite_generation {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) {N : ℕ} (hA : BallCap A N) (hAlf : LocallyFiniteSites A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) {M : ℕ} (hB : BallCap B M) (hBlf : LocallyFiniteSites B)
    (fgA : (AddSubgroup.closure A).FG) (fgB : (AddSubgroup.closure B).FG) :
    HasFiniteLatticeCover A := by
  classical
  by_cases hAne : A.Nonempty
  swap
  · exact ⟨1,le_rfl,fun _ => 0,fun _ => 1,by simp, fun x hx => False.elim (hAne ⟨x,hx⟩)⟩
  obtain ⟨R,_,hR⟩ := spectral_carrier_relatively_dense hA ⟨a,hμ⟩ ⟨b,hν⟩ hAne
  have hfull : span ℝ B = ⊤ := by
    by_contra hp
    obtain ⟨c,hc⟩ := exists_ball_avoiding_affine_subspaces (fun _ : Unit => span ℝ B)
      (fun _ => hp) (fun _ => 0) R
    obtain ⟨x,hx,hd⟩ := hR c
    exact hd.not_gt (hc () x (by simpa using (subset_span hx : x ∈ span ℝ B)))
  let G := span ℤ B
  have hg : G.FG := (fg_iff_addSubgroup_fg G).mpr (by
    simpa [G,span_int_eq_addSubgroupClosure] using fgB)
  obtain ⟨D,hD⟩ := hg
  let u := (fun i : Fin D.card => (D.equivFin.symm i).val)
  have hu : range u = (D : Set (Space d)) := by
    ext x; constructor
    · rintro ⟨i,rfl⟩; exact (D.equivFin.symm i).property
    · intro hx; exact ⟨D.equivFin ⟨x,hx⟩,by simp [u]⟩
  have hspan : span ℤ (range u) = G := hu ▸ hD
  have hBG : B ⊆ G := subset_span
  have hRG : span ℝ (G : Set (Space d)) = ⊤ := by rw [show G = span ℤ B from rfl,span_span_of_tower,hfull]
  obtain ⟨k,t,P,hcover,hrelations⟩ := physical_cosets_of_laurent (unitaryLaurent_of_equation
    (unitaryEquation_of_nondegenerate (nondegenerate_of_unitEquations unitaryUnitEquationFiniteness))) A
    fgA u
  let F (j : Fin k) := {x : Fin d → ℝ | WithLp.toLp 2 x - t j ∈ P j}
  refine finiteLatticeCover_of_lattice_or_subspace A (fun j => (t j).ofLp) F ?_ hcover ?_
  · intro j
    let W := span ℝ (P j : Set (Space d))
    by_cases hW : W = ⊤
    · obtain ⟨T,hT,hsub⟩ := HalfBall.spanning_coset_contained_in_lattice hμ hA hν hBlf G hBG hRG (t j) (P j) hW (hspan ▸ hrelations j)
      refine Or.inl ⟨T,hT,fun x hx => ?_⟩
      obtain ⟨z,hz⟩ := (mem_latticeCoset_iff (t j) (WithLp.toLp 2 x) T).mpr (hsub hx)
      exact ⟨z,congrArg WithLp.ofLp hz.symm⟩
    · let l := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm
      refine Or.inr ⟨W.comap l.toLinearMap,?_,fun x hx => ?_⟩
      · intro htop
        apply hW
        apply top_unique
        intro y _
        obtain ⟨x,rfl⟩ := l.surjective y
        exact (show x ∈ W.comap l.toLinearMap by rw [htop]; trivial)
      · change l (x - (t j).ofLp) ∈ W
        rw [map_sub]
        exact subset_span hx
  · intro f hf hp
    obtain ⟨R,hR⟩ := HalfBall.relatively_dense_filtered_atoms hAlf hμ hν hB f hf hp
    refine ⟨R,fun c => ?_⟩
    obtain ⟨x,hx,hfx,hc⟩ := hR (WithLp.toLp 2 c)
    exact ⟨x,hx,hfx,(dist_pi_le_iff (dist_nonneg.trans hc)).mpr fun i => (PiLp.dist_apply_le (WithLp.toLp 2 c) x i).trans hc⟩

private theorem cover_of_matrix_cover {p} {A : Set (V p)} (h : HasFiniteLatticeCover A) : LatticeCovered A := by
  classical
  obtain ⟨m,_,t,T,hT,hs⟩ := h
  let e (i : Fin m) := (T i).toLinearEquiv' ((T i).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr (hT i))).invertible
  let L (i : Fin m) : LatticeCoset p := ⟨t i,(e i).toContinuousLinearEquiv.trans (PiLp.continuousLinearEquiv 2 ℝ _).symm⟩
  refine ⟨m,L,fun x hx => ?_⟩
  obtain ⟨i,z,he⟩ := hs x hx
  exact mem_iUnion.mpr ⟨i,z,he.symm⟩

private theorem cap_reflected {p M} {A : Set (V p)} (ha : BallCap A M) : BallCap (reflected A) M := by
  classical
  intro y T hT
  let e : V p ↪ V p := ⟨Neg.neg,neg_injective⟩
  have hh := ha (-y) (T.map e) (by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hz
    exact ⟨(hT hx).1,by simpa [e,mem_ball] using (hT hx).2⟩)
  simpa using hh

private theorem closure_reflected {p} (A : Set (V p)) : AddSubgroup.closure (reflected A) = AddSubgroup.closure A := by
  apply le_antisymm
  · exact (AddSubgroup.closure_le _).mpr fun x hx => by
      simpa using (AddSubgroup.closure A).neg_mem (AddSubgroup.subset_closure (show -x ∈ A from hx))
  · exact (AddSubgroup.closure_le _).mpr fun x hx => by
      have hh : -x ∈ reflected A := by simpa [reflected] using hx
      simpa using (AddSubgroup.closure (reflected A)).neg_mem (AddSubgroup.subset_closure hh)

/-- Both lattice covers follow from bounded unit-ball counts and finite
generation of both carrier groups. These last two hypotheses are the
finite-generation conclusions of Proposition B.2. -/
theorem lattice_covers_of_finite_generation {p M N} {μ : TemperedDistribution (V p) ℂ}
    {A B : Set (V p)} (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B)
    (ha : LocalAtoms μ A) (hb : LocalAtoms (𝓕 μ) B) (cA : BallCap A M) (cB : BallCap B N)
    (fgA : (AddSubgroup.closure A).FG) (fgB : (AddSubgroup.closure B).FG) :
    LatticeCovered A ∧ LatticeCovered B := by
  obtain ⟨r,hr⟩ := localAtoms_double_fourier ha
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  exact ⟨cover_of_matrix_cover (physical_cover_of_finite_generation ha cA hA hb cB hB fgA fgB),
    cover_of_matrix_cover (physical_cover_of_finite_generation hb cB hB hr (cap_reflected cA)
      (locallyFinite_reflected hA) fgB (closure_reflected A ▸ fgA))⟩

end HalfBall
