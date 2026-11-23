module

public import HalfBall.LocalCount
import Mathlib.Topology.Sequences
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Filter Finset
open scoped Topology
variable {p : ℕ}

def UnitSeparated (P : Finset (V p)) : Prop :=
  ∀ q ∈ P, ∀ r ∈ P, q ≠ r → 1 < dist q r

theorem exists_packing (Y : Finset (V p)) :
    ∃ Q ⊆ Y, UnitSeparated Q ∧ ∀ P ⊆ Y, UnitSeparated P → P.card ≤ Q.card := by
  classical
  let D := Y.powerset.filter UnitSeparated
  have hempty : ∅ ∈ D := mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), by simp [UnitSeparated]⟩
  obtain ⟨Q,hQ,hmax⟩ := D.exists_max_image card ⟨∅,hempty⟩
  obtain ⟨hsub,hsep⟩ := mem_filter.mp hQ
  exact ⟨Q,mem_powerset.mp hsub,hsep,fun P hP hs => hmax P (mem_filter.mpr ⟨mem_powerset.mpr hP,hs⟩)⟩

noncomputable def packing (Y : Finset (V p)) : Finset (V p) := (exists_packing Y).choose

theorem packing_spec (Y : Finset (V p)) : packing Y ⊆ Y ∧ UnitSeparated (packing Y) ∧
    ∀ P ⊆ Y, UnitSeparated P → P.card ≤ (packing Y).card := (exists_packing Y).choose_spec

/-- Choose a single subsequence of all packing fractions before introducing
any anchor. Zero limits and positive limits refer to this same subsequence. -/
theorem packing_subsequence {L : ℕ} (Y : ℕ → Fin L → Finset (V p)) (N : ℕ → ℝ)
    (C : ℝ) (hN : ∀ n, 0 < N n) (hY : ∀ n i, ((Y n i).card : ℝ) ≤ C * N n) :
    ∃ (φ : ℕ → ℕ) (a : Fin L → ℝ), StrictMono φ ∧ (∀ i, a i ∈ Set.Icc 0 C) ∧
      ∀ i, Tendsto (fun n => ((packing (Y (φ n) i)).card : ℝ) / N (φ n)) atTop (𝓝 (a i)) := by
  let f (n : ℕ) (i : Fin L) := ((packing (Y n i)).card : ℝ) / N n
  have hmem (n) : f n ∈ Set.Icc (fun _ => 0) (fun _ => C) := by
    constructor
    · intro i; dsimp [f]; positivity [hN n]
    · intro i
      apply (div_le_iff₀ (hN n)).mpr
      exact (by exact_mod_cast card_le_card (packing_spec (Y n i)).1 :
        ((packing (Y n i)).card : ℝ) ≤ (Y n i).card).trans (hY n i)
  obtain ⟨a,ha,φ,hφ,hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  exact ⟨φ,a,hφ,fun i => ⟨ha.1 i,ha.2 i⟩,tendsto_pi_nhds.mp hlim⟩

/-- Cubical volume at the measured radius. Each side is S/(3√p). -/
noncomputable def scaleVolume (p : ℕ) (S : ℝ) : ℝ := (S / (3 * Real.sqrt p)) ^ p

/-- The output needed from A.5. All labels and constants are fixed before
the anchor; signs and labels witnessing a representation may vary with it.
A single positive lower packing fraction suffices because there are only
finitely many retained labels. -/
def HasRepresentations (B : Set (V p)) (η : V p) (S : ℕ → ℝ) : Prop :=
  ∃ (φ : ℕ → ℕ) (L : ℕ) (Y : ℕ → Fin L → Finset (V p)) (K C δ β : ℝ),
    StrictMono φ ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ 0 < β ∧
    (∀ᶠ j in atTop, ∀ i, (↑(Y j i) : Set (V p)) ⊆ B ∩ halfBall η (S (φ j))) ∧
    (∀ᶠ j in atTop, (Pairwise fun i k => Disjoint (Y j i) (Y j k))) ∧
    (∀ᶠ j in atTop, ∀ i, PieceBounds (Y j i) (scaleVolume p (S (φ j))) K C δ) ∧
    ∀ s ∈ B ∩ halfSpace η, ∀ᶠ j in atTop, ∃ u : Tuple L, qualifies (Y j) (scaleVolume p (S (φ j))) β u s

/-- A.6 and the finite-maximum step of A.3, from A.5's representation data. -/
theorem geometric_local_count_of_representations (hp : 0 < p) {B : Set (V p)} {η : V p}
    {S : ℕ → ℝ} (hS : ∀ j, 0 < S j) (h : HasRepresentations B η S) :
    ∃ M, BallCap (B ∩ halfSpace η) M := by
  obtain ⟨φ,L,Y,K,C,δ,β,_,hK,hC,hδ,hβ,_,_,hY,hs⟩ := h
  obtain ⟨M,hM⟩ := represented_ball_cap p L K C δ β hK hC hδ hβ
  refine ⟨M, cap_of_eventually_qualifying hs ?_⟩
  filter_upwards [hY] with j hj
  exact hM _ _ (by unfold scaleVolume; positivity [hS (φ j)]) hj

end HalfBall
