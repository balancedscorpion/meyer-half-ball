module
public import HalfBall.Weights.LatticeGeometry
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall.Weights
open Set Filter Metric Finset Submodule
open MeyerGeneralProblem.LevOlevskii
open scoped Topology

/-- Take a common subsequence of representatives modulo finitely many
lattices. The translated lattice positions then have simultaneous limits. -/
private theorem limiting_positions {p k} (T : Fin k → Mat p) (hT : ∀ i, (T i).det ≠ 0) (y : ℕ → V p) :
    ∃ (θ : ℕ → ℕ) (r : Fin k → V p) (h : ℕ → Fin k → V p), StrictMono θ ∧
      (∀ n i, h n i ∈ matrixLattice (T i)) ∧ ∀ i, Tendsto (fun n => y (θ n)-h n i) atTop (𝓝 (r i)) := by
  choose K hK hrep using fun i => matrix_fundamental_region (T i) (hT i)
  choose l hl hr using fun n i => hrep i (y n)
  obtain ⟨r,_,θ,hθ,ht⟩ := (isCompact_univ_pi (fun i => (hK i).isCompact_closure)).tendsto_subseq
    (x := fun n i => y n-l n i) (fun n i _ => subset_closure (hr n i))
  exact ⟨θ,r,fun n => l (θ n),hθ,fun n => hl (θ n),fun i => (tendsto_pi_nhds.mp ht) i⟩

private theorem eventually_away {p} {a r v : V p} {T : Mat p} (hT : T.det ≠ 0)
    {y h : ℕ → V p} (hh : ∀ n, h n ∈ matrixLattice T) (ht : Tendsto (fun n => y n-h n) atTop (𝓝 r))
    (hn : r-v ∉ coset a T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ z ∈ coset a T, δ ≤ dist z (y n-v) := by
  obtain ⟨d,hd,hsep⟩ := latticeCoset_uniformlyDiscrete a T hT
  have hclosed : IsClosed (coset a T) := Metric.isClosed_of_pairwise_le_dist hd hsep
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hn)
  have ht' := ht.sub_const v
  refine ⟨ε/2,by positivity,?_⟩
  filter_upwards [(Metric.tendsto_nhds.mp ht') (ε/2) (by positivity)] with n hdist
  intro z hz
  by_contra! hnear
  have hm : z-h n ∈ coset a T := period_sub hz (hh n)
  apply hball (a := z-h n) _ hm
  change dist (z-h n) (r-v) < ε
  have he : (y n-v)-h n = y n-h n-v := by abel
  have hds := dist_sub_right z (y n-v) (h n)
  rw [he] at hds
  exact (dist_triangle _ (y n-h n-v) _).trans_lt (by change dist (y n-h n-v) (r-v) < ε/2 at hdist; linarith)

/-- Along a common subsequence, sites near a fixed translated location
are uniformly isolated unless the displacement belongs to a finite union
of proper affine subspaces. Distinct sites from commensurate cosets already
have a uniform gap, so they produce no exceptional subspaces. -/
theorem collision_flats {p k} (a : Fin k → V p) (T : Fin k → Mat p) (hT : ∀ i, (T i).det ≠ 0)
    (y : ℕ → V p) : ∃ (θ : ℕ → ℕ), StrictMono θ ∧ ∃ (κ : Type) (_ : Fintype κ)
      (W : κ → Submodule ℝ (V p)) (c : κ → V p), (∀ i, W i ≠ ⊤) ∧
      ∀ v : V p, (∀ i, v-c i ∉ W i) → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
        ∀ i, y (θ n)-v ∈ coset (a i) (T i) → ∀ j z, z ∈ coset (a j) (T j) →
          z ≠ y (θ n)-v → δ ≤ dist z (y (θ n)-v) := by
  classical
  obtain ⟨θ,r,h,hθ,hh,ht⟩ := limiting_positions T hT y
  let C i := coset (a i) (T i)
  let good (ij : Fin k × Fin k) := ∃ d : ℝ, 0 < d ∧
    ∀ x ∈ C ij.1, ∀ z ∈ C ij.2, x ≠ z → d ≤ dist x z
  let hits (ij : Fin k × Fin k) (v : V p) := r ij.1-v ∈ C ij.1 ∧ r ij.2-v ∈ C ij.2
  let J := {ij : Fin k × Fin k // ¬good ij ∧ ∃ v, hits ij v}
  choose c hc using fun j : J => j.property.2
  choose W hW hcom using fun j : J => (pair_alternative (a j.val.1) (a j.val.2) (T _) (T _)
    (hT j.val.1) (hT j.val.2)).resolve_left j.property.1
  have hflat (j : J) {v} (hv : hits j.val v) : v-c j ∈ W j := by
    apply hcom j
    · have hmem := (matrixLattice (T j.val.1)).sub_mem ((mem_latticeCoset_iff ..).mp (hc j).1)
        ((mem_latticeCoset_iff ..).mp hv.1)
      convert hmem using 1
      abel
    · have hmem := (matrixLattice (T j.val.2)).sub_mem ((mem_latticeCoset_iff ..).mp (hc j).2)
        ((mem_latticeCoset_iff ..).mp hv.2)
      convert hmem using 1
      abel
  refine ⟨θ,hθ,J,inferInstance,W,c,hW,fun v hv => ?_⟩
  have hb (ij : Fin k × Fin k) : ∃ d : ℝ, 0 < d ∧ ∀ᶠ n in atTop,
      y (θ n)-v ∈ C ij.1 → ∀ z ∈ C ij.2, z ≠ y (θ n)-v → d ≤ dist z (y (θ n)-v) := by
    by_cases hg : good ij
    · obtain ⟨d,hd,hh⟩ := hg
      exact ⟨d,hd,Eventually.of_forall fun n hn z hz hne => (dist_comm (y (θ n)-v) z) ▸ hh _ hn z hz hne.symm⟩
    have hnot : ¬hits ij v := fun h => hv (⟨ij,hg,v,h⟩ : J) (hflat _ h)
    by_cases h₁ : r ij.1-v ∈ C ij.1
    · obtain ⟨d,hd,hdist⟩ := eventually_away (hT ij.2) (fun n => hh n ij.2) (ht ij.2) (fun h₂ => hnot ⟨h₁,h₂⟩)
      exact ⟨d,hd,hdist.mono fun _ h _ z hz _ => h z hz⟩
    · obtain ⟨d,hd,hdist⟩ := eventually_away (hT ij.1) (fun n => hh n ij.1) (ht ij.1) h₁
      exact ⟨d,hd,hdist.mono fun n h hn => False.elim (hd.not_ge (by simpa using h _ hn))⟩
  choose d hd hgood using hb
  obtain ⟨δ,hδ,_,hmin⟩ := finite_gap univ d
  refine ⟨δ,hδ,?_⟩
  filter_upwards [eventually_all.mpr hgood] with n hn
  intro i hi j z hz hne
  exact (by simpa [abs_of_pos (hd (i,j))] using hmin (i,j) (mem_univ _) (hd _).ne' : δ ≤ d (i,j)) |>.trans (hn (i,j) hi z hz hne)

end HalfBall.Weights
