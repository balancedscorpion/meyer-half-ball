module

public import HalfBall.Recurrence
public import HalfBall.AnchoredTriangles
public import HalfBall.Representations
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Finset
open scoped InnerProductSpace

/-- Move each finite cluster into the measured half-space by a common
approximate return. Only the chosen finite cluster needs a separation margin. -/
theorem global_ball_cap {p : ℕ} (hp : 0 < p) {B : Set (V p)} {η : V p} {S : ℕ → ℝ}
    (hB : LocallyFiniteSites B) (hη : ‖η‖ = 1) (hpatch : OrderedPatchBound B)
    (hS : HalfBallCount B η S) : ∃ M : ℕ, BallCap B M := by
  classical
  obtain ⟨M,hM⟩ := geometric_local_count_of_anchored_triangles hp hB hS
    (anchored_triangle_bound hp hB hη hpatch hS)
  refine ⟨M,fun y F hF => ?_⟩
  obtain ⟨r,hr,_,hsep⟩ := finite_gap (F ×ˢ F) (fun q => dist q.1 q.2)
  obtain ⟨d,hd,_,hboundary⟩ := finite_gap F (fun f => 1 - dist f y)
  let ε := min r d / 3
  have hε : 0 < ε := by dsimp [ε]; positivity
  have her : 2*ε < r := by dsimp [ε]; linarith [min_le_left r d]
  have hed : ε < d := by dsimp [ε]; linarith [min_le_right r d]
  obtain ⟨L,hL,hreturn⟩ := pattern_recurrence hB hpatch F (fun _ hf => (hF hf).1) hε
  let z := (L+2) • η
  obtain ⟨t,ht,hall⟩ := hreturn (z-y)
  choose g hg using fun f : F => hall f f.property
  have hgy (f : F) : dist (g f) (y+t) < 1 := by
    have hfy : dist (f : V p) y < 1 := (hF f.property).2
    have hmargin := hboundary f f.property (by linarith)
    rw [abs_of_pos (by linarith)] at hmargin
    have hdist := dist_triangle (g f) (f.val+t) (y+t)
    rw [dist_add_right] at hdist
    linarith [(hg f).2]
  have hyt : dist (y+t) z < L := by
    rw [dist_eq_norm] at ht ⊢
    convert ht using 2
    abel
  have hside (f : F) : g f ∈ halfSpace η := by
    have hbz : dist (g f) z < L+1 := by linarith [dist_triangle (g f) (y+t) z,hgy f]
    have hab := abs_real_inner_le_norm η (g f-z)
    rw [hη,one_mul,inner_sub_right] at hab
    have hx : ⟪η,z⟫_ℝ = L+2 := by simp [z,real_inner_smul_right,hη]
    rw [hx] at hab
    change 0 ≤ ⟪η,g f⟫_ℝ
    rw [dist_eq_norm] at hbz
    linarith [(abs_le.mp hab).1]
  have hinj : Function.Injective g := by
    intro f s hgs
    by_contra hne
    have hdif : (f : V p) ≠ s := fun h => hne (Subtype.ext h)
    have hlow := hsep (f.val,s.val) (mem_product.mpr ⟨f.property,s.property⟩) (dist_ne_zero.mpr hdif)
    simp only [abs_of_nonneg dist_nonneg] at hlow
    have hdist := dist_triangle (f.val+t) (g f) (s.val+t)
    rw [dist_add_right,dist_comm _ (g f)] at hdist
    linarith [(hg f).2, show dist (g f) (s.val+t) < ε from hgs ▸ (hg s).2]
  let Q := (univ : Finset F).image g
  have hc := hM (y+t) Q (by
    intro b hb
    obtain ⟨f,_,rfl⟩ := mem_image.mp hb
    exact ⟨⟨(hg f).1,hside f⟩,hgy f⟩)
  simpa [Q,Finset.card_image_of_injective _ hinj] using hc

/-- An actual cardinality bound on all balls, including those centred on the
opposite side of the hyperplane. -/
theorem global_local_count {p : ℕ} (hp : 0 < p) {B : Set (V p)} {η : V p} {S : ℕ → ℝ}
    (hB : LocallyFiniteSites B) (hη : ‖η‖ = 1)
    (hpatch : OrderedPatchBound B) (hS : HalfBallCount B η S) :
    ∃ M : ℕ, ∀ y : V p, (B ∩ Metric.ball y 1).ncard ≤ M := by
  obtain ⟨M,hM⟩ := global_ball_cap hp hB hη hpatch hS
  refine ⟨M,fun y => ?_⟩
  have hf : (B ∩ Metric.ball y 1).Finite :=
    (hB _ (isCompact_closedBall y 1)).subset fun _ h => ⟨h.1,Metric.ball_subset_closedBall h.2⟩
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact hM y hf.toFinset (by simp)

end HalfBall
