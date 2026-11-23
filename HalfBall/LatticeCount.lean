module

public import HalfBall.Statement
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Finset Filter

/-- A basis is specified by the invertible real coordinate map from the
standard integer grid. The translation and the basis may differ in each term. -/
structure LatticeCoset (p : ℕ) where
  shift : V p
  basis : (Fin p → ℝ) ≃L[ℝ] V p

namespace LatticeCoset
variable {p : ℕ} (L : LatticeCoset p)

/-- Site with lattice coordinate z. -/
def site (z : Fin p → ℤ) : V p := L.shift + L.basis (fun k => (z k : ℝ))

/-- A finite set covering the portion in a closed ball. Its size bound
does not depend on the centre or on the translate of the lattice. -/
theorem finite_window (y : V p) {R : ℝ} (hR : 1 ≤ R) :
    ∃ F : Finset (V p), Set.range L.site ∩ Metric.closedBall y R ⊆ ↑F ∧
      (F.card : ℝ) ≤ (2 * ‖L.basis.symm.toContinuousLinearMap‖ + 4)^p * R^p := by
  classical
  let D := ‖L.basis.symm.toContinuousLinearMap‖
  let b := ⌈D*R⌉₊
  let c := L.basis.symm (y-L.shift)
  let W (i : Fin p) := Icc (⌊c i⌋ - (b:ℤ)) (⌊c i⌋ + b + 1)
  let I := Fintype.piFinset W
  refine ⟨I.image L.site, ?_, ?_⟩
  · rintro _ ⟨⟨z,rfl⟩,hz⟩
    apply mem_image_of_mem
    apply Fintype.mem_piFinset.mpr
    intro i
    have he : L.basis.symm (L.site z-y) = (fun k => (z k:ℝ)) - c := by
      rw [show L.site z-y = L.basis (fun k => (z k:ℝ)) - (y-L.shift) by unfold site; abel]
      simp [c]
    have hn := L.basis.symm.toContinuousLinearMap.le_opNorm (L.site z-y)
    change ‖L.basis.symm (L.site z-y)‖ ≤ D * ‖L.site z-y‖ at hn
    rw [he] at hn
    have hz' : ‖L.site z-y‖ ≤ R := by simpa [Metric.mem_closedBall,dist_eq_norm] using hz
    have hpi := norm_le_pi_norm ((fun k => (z k:ℝ)) - c) i
    have hcoords : |(z i:ℝ)-c i| ≤ (b:ℝ) := hpi.trans
      (hn.trans ((mul_le_mul_of_nonneg_left hz' (norm_nonneg _)).trans (Nat.le_ceil _)))
    have hfloor := Int.floor_le (c i)
    have hnext := Int.lt_floor_add_one (c i)
    change z i ∈ Icc _ _
    apply mem_Icc.mpr
    constructor
    · exact_mod_cast (by linarith [(abs_le.mp hcoords).1] : (⌊c i⌋:ℝ) - (b:ℝ) ≤ z i)
    · exact_mod_cast (by linarith [(abs_le.mp hcoords).2] : (z i:ℝ) ≤ (⌊c i⌋:ℝ) + (b:ℝ) + 1)
  · have hc (i) : (W i).card = 2*b+2 := by dsimp [W]; rw [Int.card_Icc]; omega
    have hI : I.card = (2*b+2)^p := by simp [I,Fintype.card_piFinset,hc]
    have hb : (b:ℝ) < D*R+1 := Nat.ceil_lt_add_one (mul_nonneg (norm_nonneg _) (by linarith))
    have hr : ((2*b+2:ℕ):ℝ) ≤ (2*D+4)*R := by push_cast; nlinarith
    rw [← mul_pow]
    exact (Nat.cast_le.mpr (card_image_le (f := L.site) (s := I))).trans
      (by rw [hI,Nat.cast_pow]; exact pow_le_pow_left₀ (by positivity) hr p)

end LatticeCoset

/-- A finite cover by translates of full-rank lattices. No separation
between sites from different translates is required. -/
def LatticeCovered {p} (A : Set (V p)) : Prop :=
  ∃ m : ℕ, ∃ L : Fin m → LatticeCoset p, A ⊆ ⋃ i, Set.range (L i).site

/-- Simultaneous polynomial bound in every translated closed ball.
Taking a subset allows coincident comb sites and cancellation of their weights. -/
theorem lattice_cover_count {p} {A : Set (V p)} (h : LatticeCovered A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V p, ∀ R : ℝ, 1 ≤ R →
    (A ∩ Metric.closedBall y R).Finite ∧ ((A ∩ Metric.closedBall y R).ncard : ℝ) ≤ C*R^p := by
  classical
  obtain ⟨m,L,hA⟩ := h
  let K (i : Fin m) := (2*‖(L i).basis.symm.toContinuousLinearMap‖ + 4)^p
  refine ⟨∑ i, K i, Finset.sum_nonneg (fun i _ => by dsimp [K]; positivity), fun y R hR => ?_⟩
  choose F hF hc using fun i => (L i).finite_window y hR
  let T := univ.biUnion F
  have hsub : A ∩ Metric.closedBall y R ⊆ (↑T : Set (V p)) := by
    rintro x ⟨hx,hy⟩
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hA hx)
    exact mem_biUnion.mpr ⟨i,mem_univ _,hF i ⟨hi,hy⟩⟩
  refine ⟨T.finite_toSet.subset hsub,?_⟩
  have hb := Set.ncard_le_ncard hsub T.finite_toSet
  rw [Set.ncard_coe_finset] at hb
  calc ((A ∩ Metric.closedBall y R).ncard : ℝ) ≤ T.card := by exact_mod_cast hb
       _ ≤ ∑ i, ((F i).card:ℝ) := by exact_mod_cast (card_biUnion_le : T.card ≤ ∑ i, (F i).card)
       _ ≤ ∑ i, K i*R^p := sum_le_sum fun i _ => hc i
       _ = _ := (sum_mul ..).symm

theorem locallyFinite_of_lattice_cover {p} {A : Set (V p)} (h : LatticeCovered A) :
    LocallyFiniteSites A := by
  intro K hK
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_closedBall_lt 1 0
  obtain ⟨_,_,hc⟩ := lattice_cover_count h
  exact (hc 0 R hR.le).1.subset fun _ hx => ⟨hx.1,hKR hx.2⟩

/-- Lattice covers supply the half-ball count in every direction along every
positive divergent sequence. The same closed-ball estimate works for all of them. -/
theorem halfBallCount_of_lattice_cover {p} {A : Set (V p)} (h : LatticeCovered A)
    (η : V p) {S : ℕ → ℝ} (hpos : ∀ j, 0 < S j) (hS : Tendsto S atTop atTop) :
    HalfBallCount A η S := by
  obtain ⟨C,hC,hcount⟩ := lattice_cover_count h
  refine ⟨hpos,hS,C,hC,?_⟩
  filter_upwards [hS.eventually_ge_atTop 1] with j hj
  obtain ⟨hf,hb⟩ := hcount 0 _ hj
  exact (Nat.cast_le.mpr (Set.ncard_le_ncard (fun _ h' => ⟨h'.1,h'.2.2⟩ :
    A ∩ halfBall η (S j) ⊆ A ∩ Metric.closedBall 0 (S j)) hf)).trans hb

end HalfBall
