module
public import HalfBall.Weights.CollisionLimits
public import HalfBall.Weights.Annihilator
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall.Weights
open Set Finset Filter Metric FourierTransform
open MeyerGeneralProblem.LevOlevskii
open scoped FourierTransform Topology

/-- A finite recurrence controls a large spectral weight by values at
nonzero displacements. Choose these displacements after taking the common
subsequence of lattice positions. All the shifted weights are then either
zero or uniformly isolated. -/
theorem spectral_weights_bounded {p M} {μ : TemperedDistribution (V p) ℂ} {A B : Set (V p)}
    {a : A → ℂ} {b : B → ℂ} (ha : HasLocallyAtomicExpansion μ A a)
    (hb : HasLocallyAtomicExpansion (𝓕 μ) B b) (cap : BallCap B M)
    (coverA : HasFiniteLatticeCover A) (coverB : HasFiniteLatticeCover B) :
    ∃ C : ℝ, ∀ x : B, ‖b x‖ ≤ C := by
  classical
  have hA := locallyFinite_of_lattice_cover (latticeCovered_of_matrixCover coverA)
  have hB := locallyFinite_of_lattice_cover (latticeCovered_of_matrixCover coverB)
  obtain ⟨b',hb'⟩ := localAtoms_double_fourier ⟨a,ha⟩
  obtain ⟨m,_,t,T,hT,hcovA⟩ := coverA
  obtain ⟨k,_,s,U,hU,hcovB⟩ := coverB
  have memB (x) (hx : x ∈ B) : ∃ i, x ∈ coset (s i) (U i) := by
    obtain ⟨i,z,hz⟩ := hcovB x hx
    exact ⟨i,z,hz.symm⟩
  by_contra! h
  choose x hx using fun n : ℕ => h (n : ℝ)
  obtain ⟨θ,hθ,κ,inst,W,q,hW,hgap⟩ := collision_flats s U hU (fun n => (x n).val)
  let := inst
  obtain ⟨v,hv,havoid⟩ := avoiding_subset_sums univ (fun i => dualMatrix (T i))
    (fun i => dualMatrix_det_ne_zero _ (hT i)) W hW q
  obtain ⟨c,hc,hrel⟩ := lattice_annihilator ha hb cap t T hT (fun z hz => by
    obtain ⟨i,l,hl⟩ := hcovA z hz
    exact ⟨i,l,hl.symm⟩) v hv
  let z (n : ℕ) (J : Finset (Fin m)) := (x (θ n)).val-∑ j ∈ J,v j
  let F := (univ : Finset (Finset (Fin m))).erase ∅
  have eventual_bound (J : ↥F) : ∃ C : ℝ, ∀ᶠ n in atTop, ‖recordWeight b (z n J)‖ ≤ C := by
    have hn : J.val.Nonempty := nonempty_iff_ne_empty.mpr (ne_of_mem_erase J.property)
    obtain ⟨δ,hd,hiso⟩ := hgap _ (havoid J.val (subset_univ _) hn)
    obtain ⟨C,hC⟩ := bounded_at_isolated_sites hb hb' hB (locallyFinite_reflected hA) cap hd
    refine ⟨max C 0,?_⟩
    filter_upwards [hiso] with n hsep
    by_cases hz : z n J ∈ B
    · obtain ⟨i,hi⟩ := memB _ hz
      simpa [recordWeight,hz] using (hC ⟨z n J,hz⟩ fun w hw hne => by
        obtain ⟨j,hj⟩ := memB _ hw
        exact hsep i hi j w hj hne).trans (le_max_left C 0)
    · simp [recordWeight,hz]
  choose C hC using eventual_bound
  let S := ∑ J : ↥F, ‖c J.val‖ * C J
  obtain ⟨N,hN⟩ := exists_nat_gt (S/‖c ∅‖)
  obtain ⟨n,hn,hbig⟩ := ((eventually_all.mpr hC).and (hθ.tendsto_atTop.eventually_ge_atTop N)).exists
  have hlarge : S < ‖c ∅‖ * ‖b (x (θ n))‖ := by
    rw [mul_comm,← div_lt_iff₀ (norm_pos_iff.mpr hc)]
    exact hN.trans ((Nat.cast_le.mpr hbig).trans_lt (hx _))
  have eqn := hrel (x (θ n)).val
  rw [← sum_erase_add _ _ (mem_univ (∅ : Finset (Fin m)))] at eqn
  simp only [sum_empty,sub_zero,recordWeight,dite_eq_left (x (θ n)).property] at eqn
  have hrest : ∑ J ∈ F, c J * recordWeight b (z n J) = -(c ∅ * b (x (θ n))) :=
    eq_neg_of_add_eq_zero_left eqn
  have hs : ‖c ∅‖ * ‖b (x (θ n))‖ ≤ S := by
    rw [← norm_mul,← norm_neg,← hrest,← sum_attach]
    exact (norm_sum_le ..).trans (sum_le_sum fun J _ => by rw [norm_mul]; gcongr; exact hn J)
  exact hlarge.not_ge hs

end HalfBall.Weights
