module

public import HalfBall.Combinatorics.CellSampling
public import HalfBall.Combinatorics.IndependentSet
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Finset SimpleGraph

variable {α κ : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]

def trianglesAt (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :=
  ((G.neighborFinset v) ×ˢ (G.neighborFinset v)).filter fun z => G.Adj z.1 z.2

private def selected {ι : Type*} (E : Finset ι) (cells : ι → Finset κ) (ω : κ → Bool) :=
  E.filter fun x => ∀ i ∈ cells x, ω i = true

/-- Coarse-cell sampling and deletion for the fine graph. Each fine vertex has
a list of forbidden coarse partners, and each fine edge joins different coarse
cells. The lower bound charges all ordered triangles before deletion. -/
theorem sample_independent (G : SimpleGraph α) [DecidableRel G.Adj]
    (c : α → κ) (bad : α → Finset κ) (hbad : ∀ v, c v ∉ bad v)
    (hcross : ∀ v w, G.Adj v w → c v ≠ c w) (q : ℝ) (hq : q ∈ Set.Icc 0 1)
    (k D : ℕ) (hD : 0 < D) (hk : k*(2^k+1) ≤ 4*D) :
    ∃ I : Finset α, G.IsIndepSet (↑I) ∧ (∀ v ∈ I, ∀ w ∈ I, c w ∉ bad v) ∧
      k * (∑ v : α, (q - (bad v).card*q^2 - (G.degree v)*q^2/D -
        (trianglesAt G v).card*q^3)) ≤ 8*D*(I.card : ℝ) := by
  classical
  let P (ω : κ → Bool) := univ.filter (fun v => ω (c v) = true)
  let B v := selected (bad v) (fun b => {c v,b})
  let E v := selected (G.neighborFinset v) (fun w => {c v,c w})
  let T v := selected (trianglesAt G v) (fun z => {c v,c z.1,c z.2})
  let score v (ω : κ → Bool) : ℝ := (if ω (c v) = true then 1 else 0) -
    (B v ω).card - (1/(D : ℝ))*(E v ω).card - (T v ω).card
  have hmean (v : α) : cellMean q (score v) =
      q - (bad v).card*q^2 - (G.degree v)*q^2/D - (trianglesAt G v).card*q^3 := by
    have hp : cellMean q (fun ω => if ω (c v) = true then 1 else 0) = q := by
      simpa using cellMean_event q ({c v} : Finset κ)
    have hb : cellMean q (fun ω => ((B v ω).card : ℝ)) = (bad v).card*q^2 := by
      dsimp only [B,selected]
      rw [cellMean_count q (bad v) (fun b => {c v,b})]
      have hc b (hb : b ∈ bad v) : ({c v,b} : Finset κ).card = 2 := by
        exact card_pair (show c v ≠ b from fun h => hbad v (h.symm ▸ hb))
      simp [sum_congr rfl (fun b hb => congrArg (q^·) (hc b hb))]
    have he : cellMean q (fun ω => ((E v ω).card : ℝ)) = (G.degree v)*q^2 := by
      dsimp only [E,selected]
      rw [cellMean_count q (G.neighborFinset v) (fun w => {c v,c w})]
      have hc w (hw : w ∈ G.neighborFinset v) : ({c v,c w} : Finset κ).card = 2 :=
        card_pair (hcross _ _ ((G.mem_neighborFinset ..).mp hw))
      simp [sum_congr rfl (fun w hw => congrArg (q^·) (hc w hw))]
    have ht : cellMean q (fun ω => ((T v ω).card : ℝ)) = (trianglesAt G v).card*q^3 := by
      dsimp only [T,selected]
      rw [cellMean_count q (trianglesAt G v) (fun z => {c v,c z.1,c z.2})]
      have hc z (hz : z ∈ trianglesAt G v) : ({c v,c z.1,c z.2} : Finset κ).card = 3 := by
        obtain ⟨hz,h12⟩ := mem_filter.mp hz
        obtain ⟨h1,h2⟩ := mem_product.mp hz
        simp [hcross _ _ ((G.mem_neighborFinset ..).mp h1),
          hcross _ _ ((G.mem_neighborFinset ..).mp h2),hcross _ _ h12]
      simp [sum_congr rfl (fun z hz => congrArg (q^·) (hc z hz))]
    unfold score
    rw [cellMean_sub,cellMean_sub,cellMean_sub,cellMean_mul,hp,hb,he,ht]
    ring
  let total ω := ∑ v, score v ω
  obtain ⟨ω,hω⟩ := exists_ge_cellMean hq total
  have havg : cellMean q total = ∑ v : α, cellMean q (score v) := by
    simp only [cellMean,total,mul_sum]
    rw [sum_comm]
  let keep := (P ω).filter fun v => B v ω = ∅ ∧ (E v ω).card ≤ D ∧ T v ω = ∅
  have hscore (v : α) : score v ω ≤ if v ∈ keep then 1 else 0 := by
    have hB : 0 ≤ ((B v ω).card : ℝ) := by positivity
    have hE : 0 ≤ 1/(D : ℝ)*(E v ω).card := by positivity
    have hT : 0 ≤ ((T v ω).card : ℝ) := by positivity
    by_cases hv : ω (c v) = true
    · by_cases hh : v ∈ keep
      · simp only [score,hv,hh,ite_true]; linarith
      · have hf := hh
        simp only [keep,P,mem_filter,mem_univ,true_and,hv,true_and] at hf
        simp only [score,hv,ite_true,hh,ite_false]
        by_cases h : B v ω = ∅
        · by_cases he : (E v ω).card ≤ D
          · have ht : T v ω ≠ ∅ := fun ht => hf ⟨h,he,ht⟩
            have ht' : 1 ≤ ((T v ω).card : ℝ) := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr ht)
            linarith
          · have he' : (D : ℝ) ≤ (E v ω).card := by exact_mod_cast (le_of_not_ge he)
            have hd' : (0 : ℝ) < D := by exact_mod_cast hD
            have he'' : 1 ≤ 1/(D : ℝ)*(E v ω).card := by rw [one_div,inv_mul_eq_div]; exact (one_le_div hd').mpr he'
            linarith
        · have h' : 1 ≤ ((B v ω).card : ℝ) := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr h)
          linarith
    · have hh : v ∉ keep := fun h => hv (mem_filter.mp (mem_filter.mp h).1).2
      unfold score
      rw [ite_eq_right hv,ite_eq_right hh]; linarith
  have hactive {v} (h : v ∈ keep) : ω (c v) = true := (mem_filter.mp (mem_filter.mp h).1).2
  let H := G.induce (↑keep : Set α)
  have htfree : H.CliqueFree 3 := by
    intro t ht
    obtain ⟨a,b,d,hab,had,hbd,_⟩ := is3Clique_iff.mp ht
    have hm : (b.val,d.val) ∈ T a.val ω := by
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨(G.mem_neighborFinset ..).mpr hab,(G.mem_neighborFinset ..).mpr had⟩,hbd⟩,?_⟩
      simp [hactive a.property,hactive b.property,hactive d.property]
    rw [(mem_filter.mp a.property).2.2.2] at hm
    exact notMem_empty _ hm
  have hdeg (v : (↑keep : Set α)) : H.degree v ≤ D := by
    have hle : H.degree v ≤ (E v.val ω).card := card_le_card_of_injOn Subtype.val
      (fun w hw => mem_filter.mpr ⟨(G.mem_neighborFinset ..).mpr ((H.mem_neighborFinset ..).mp hw),
        by simp [hactive v.property,hactive w.property]⟩) Subtype.val_injective.injOn
    exact hle.trans (mem_filter.mp v.property).2.2.1
  obtain ⟨I,hi,hcap⟩ := triangle_free_independent_set H htfree k D hk hdeg
  refine ⟨I.image Subtype.val,?_,?_,?_⟩
  · rintro v hv w hw hvw
    obtain ⟨v,hvI,rfl⟩ := mem_image.mp (show v ∈ I.image Subtype.val from hv)
    obtain ⟨w,hwI,rfl⟩ := mem_image.mp (show w ∈ I.image Subtype.val from hw)
    exact hi hvI hwI (fun e => hvw (congrArg Subtype.val e))
  · rintro v hv w hw hb
    obtain ⟨v,_,rfl⟩ := mem_image.mp hv
    obtain ⟨w,_,rfl⟩ := mem_image.mp hw
    have hm : c w.val ∈ B v.val ω := mem_filter.mpr ⟨hb,by simp [hactive v.property,hactive w.property]⟩
    rw [(mem_filter.mp v.property).2.1] at hm
    exact notMem_empty _ hm
  · rw [card_image_of_injective _ Subtype.val_injective]
    rw [havg] at hω
    simp_rw [hmean] at hω
    have hS : total ω ≤ keep.card := by simpa [sum_boole] using sum_le_sum (s := univ) (fun v _ => hscore v)
    have hcard : k*keep.card ≤ 8*D*I.card := by simpa using hcap
    exact (mul_le_mul_of_nonneg_left (hω.trans hS) (by positivity)).trans (by exact_mod_cast hcard)

end HalfBall
