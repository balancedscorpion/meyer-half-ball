module

public import HalfBall

@[expose] public section
namespace HalfBall

/-- Theorem A.3 (geometric local count). The same integer works in every open
unit ball. The centre ranges over all Euclidean space and sites on the
bounding hyperplane are included. -/
theorem geometric_local_count {p : ℕ} (hp : 0 < p) (B : Set (V p)) (η : V p) (S : ℕ → ℝ)
    (hB : LocallyFiniteSites B) (hη : ‖η‖ = 1)
    (hpatch : OrderedPatchBound B) (hS : HalfBallCount B η S) :
    ∃ M : ℕ, ∀ y : V p, ((B ∩ halfSpace η) ∩ Metric.ball y 1).ncard ≤ M := by
  obtain ⟨M,hM⟩ := geometric_local_count_of_anchored_triangles hp hB hS
    (anchored_triangle_bound hp hB hη hpatch hS)
  refine ⟨M,fun y => ?_⟩
  have hf : ((B ∩ halfSpace η) ∩ Metric.ball y 1).Finite :=
    (hB _ (isCompact_closedBall y 1)).subset fun _ h => ⟨h.1.1,Metric.ball_subset_closedBall h.2⟩
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact hM y hf.toFinset (by simp)

end HalfBall
