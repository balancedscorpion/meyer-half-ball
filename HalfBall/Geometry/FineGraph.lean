module

public import HalfBall.Geometry.Mesh
public import HalfBall.Combinatorics.Pruning
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Finset SimpleGraph
variable {p m n : ℕ}

/-- The oriented contact test between two fine cells may overcount edges.
Symmetry of the offset list turns it into an undirected graph. -/
def fineGraph (m : ℕ) (t : ℝ) (F : Finset (V p)) (hF : ∀ h ∈ F, -h ∈ F) :
    SimpleGraph (Grid p m) where
  Adj v w := v ≠ w ∧ ∃ h ∈ F, Near (corner t w) (corner t v + h) t
  symm := by
    constructor
    rintro v w ⟨hne,h,hh,hnear⟩
    refine ⟨hne.symm,-h,hF _ hh,fun i => ?_⟩
    have hi := hnear i
    change |corner t w i - (corner t v i + h i)| ≤ t at hi
    change |corner t v i - (corner t w i + -h i)| ≤ t
    rw [show corner t v i - (corner t w i + -h i) = -(corner t w i-(corner t v i+h i)) by ring,abs_neg]
    exact hi
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem fine_degree (m : ℕ) {t : ℝ} (ht : 0 < t) (F : Finset (V p)) (hF)
    [DecidableRel (fineGraph m t F hF).Adj] (v : Grid p m) :
    (fineGraph m t F hF).degree v ≤ F.card * 4^p := by
  classical
  let G := fineGraph m t F hF
  have hsub : G.neighborFinset v ⊆ F.biUnion (fun h => nearGrid m t (corner t v + h) t) := by
    intro w hw
    obtain ⟨_,h,hh,hn⟩ := (G.mem_neighborFinset v w).mp hw
    exact mem_biUnion.mpr ⟨h,hh,(mem_nearGrid ..).mpr hn⟩
  apply (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc _ ≤ ∑ _h ∈ F, 4^p := sum_le_sum (fun h _ => card_nearGrid m 1 ht (by simp) _)
       _ = _ := by simp

/-- The subgrid is fine enough to distinguish zero from all nonzero
three-offset sums. Two successive edge labels determine at most 4^(2p)
possible paths from a fixed vertex. -/
theorem fine_triangles (m : ℕ) {t : ℝ} (ht : 0 < t) (F : Finset (V p)) (hF)
    [DecidableRel (fineGraph m t F hF).Adj] (v : Grid p m)
    (hgap : ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ‖a+b+c‖ ≤ Real.sqrt p*(3*t) → a+b+c=0) :
    (trianglesAt (fineGraph m t F hF) v).card ≤ (triples F F F 0).card * (4^p)^2 := by
  classical
  let G := fineGraph m t F hF
  let next (w : Grid p m) (h : V p) := nearGrid m t (corner t w+h) t
  let paths (a b : V p) := (next v a).biUnion fun w => ({w} : Finset _) ×ˢ next w b
  have hpath a b : (paths a b).card ≤ (4^p)^2 := by
    apply card_biUnion_le.trans
    calc _ ≤ ∑ _ ∈ next v a, 4^p := sum_le_sum (fun w _ => by simpa [next] using card_nearGrid m 1 ht (by simp) (corner t w+b))
         _ = (next v a).card*(4^p) := by simp
         _ ≤ _ := by rw [sq]; gcongr; exact card_nearGrid m 1 ht (by simp) _
  have hs : trianglesAt G v ⊆ (triples F F F 0).biUnion (fun z => paths z.1 z.2.1) := by
    rintro ⟨w,u⟩ h
    obtain ⟨hm,hwu⟩ := mem_filter.mp h
    obtain ⟨hw,hu⟩ := mem_product.mp hm
    obtain ⟨_,a,ha,hn1⟩ := (G.mem_neighborFinset v w).mp hw
    obtain ⟨_,b,hb,hn2⟩ := hwu
    obtain ⟨_,c,hc,hn3⟩ := ((G.mem_neighborFinset v u).mp hu).symm
    have hz : a+b+c=0 := by
      apply hgap _ ha _ hb _ hc
      apply norm_le_of_coords _ (by positivity)
      intro i
      have h1 := abs_le.mp (hn1 i); have h2 := abs_le.mp (hn2 i); have h3 := abs_le.mp (hn3 i)
      change |a i + b i + c i| ≤ _
      change -t ≤ corner t w i - (corner t v i + a i) ∧ _ at h1
      change -t ≤ corner t u i - (corner t w i + b i) ∧ _ at h2
      change -t ≤ corner t v i - (corner t u i + c i) ∧ _ at h3
      simp only [PiLp.add_apply] at h1 h2 h3
      exact abs_le.mpr ⟨by linarith [h1.2,h2.2,h3.2],by linarith [h1.1,h2.1,h3.1]⟩
    exact mem_biUnion.mpr ⟨(a,b,c),mem_filter.mpr ⟨mem_product.mpr ⟨ha,mem_product.mpr ⟨hb,hc⟩⟩,hz⟩,
      mem_biUnion.mpr ⟨w,(mem_nearGrid ..).mpr hn1,mem_product.mpr ⟨mem_singleton_self _,(mem_nearGrid ..).mpr hn2⟩⟩⟩
  exact (card_le_card hs).trans (card_biUnion_le.trans ((sum_le_sum (fun z _ => hpath z.1 z.2.1)).trans (by simp)))

theorem fine_crosses_coarse {d t : ℝ} (hd : 0 < d) (hn : 0 < n) (ht : t = d/n)
    (F : Finset (V p)) (hF) (hsep : ∀ h ∈ F, Real.sqrt p*(2*d) < ‖h‖)
    (v w : Grid p (m*n)) (he : (fineGraph (m*n) t F hF).Adj v w) : coarse hn v ≠ coarse hn w := by
  obtain ⟨_,h,hh,hnear⟩ := he
  intro hc
  apply (not_lt_of_ge (norm_le_of_coords h (by positivity) ?_)) (hsep h hh)
  intro i
  subst t
  obtain ⟨hv,hv'⟩ := coarse_error hd hn v i
  obtain ⟨hw,hw'⟩ := coarse_error hd hn w i
  rw [hc] at hv hv'
  have he' := abs_le.mp (hnear i)
  change -(d/n) ≤ corner (d/n) w i - (corner (d/n) v i + h i) ∧
    corner (d/n) w i - (corner (d/n) v i + h i) ≤ d/n at he'
  have hsmall : d / n ≤ d := div_le_self hd.le (by exact_mod_cast hn)
  exact abs_le.mpr ⟨by linarith [he'.2],by linarith [he'.1]⟩

end HalfBall
