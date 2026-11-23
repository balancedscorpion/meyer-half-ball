module

public import HalfBall.Statement
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic

@[expose] public section

namespace HalfBall

open scoped Pointwise
open Finset

variable {p : ℕ}

/-- Once the last two coordinates are specified the first is forced. -/
noncomputable def representations (A B C : Finset (V p)) (target : V p) :=
  (B ×ˢ C).filter fun z => target - z.1 - z.2 ∈ A

/-- Count a packed site together with a representation. Inside a small ball
the encoded difference and the last two coordinates determine all the inputs. -/
theorem packing_incidence (A B C P T : Finset (V p)) (m : ℝ) (hm : m ≠ 0)
    (hP : P ⊆ A) (hsep : ∀ q ∈ P, ∀ r ∈ P, q ≠ r → 1 < dist q r)
    (hdiam : ∀ s ∈ T, ∀ t ∈ T, ‖m • (s - t)‖ ≤ 1) :
    (∑ s ∈ T, P.card * (representations A B C (m • s)).card) ≤
      (A - A).card * (B.card * C.card) := by
  classical
  let domain := T.sigma fun s => P ×ˢ representations A B C (m • s)
  let encode (w : (s : V p) × (V p × (V p × V p))) :=
    (m • w.1 - w.2.2.1 - w.2.2.2 - w.2.1, w.2.2)
  have maps : Set.MapsTo encode (↑domain) (↑((A - A) ×ˢ (B ×ˢ C))) := by
    rintro ⟨s,q,u,v⟩ hw
    obtain ⟨_,hw⟩ := mem_sigma.mp hw
    obtain ⟨hq,hr⟩ := mem_product.mp hw
    obtain ⟨huv,ha⟩ := mem_filter.mp hr
    exact mem_product.mpr ⟨sub_mem_sub ha (hP hq), huv⟩
  have inj : Set.InjOn encode (↑domain) := by
    rintro ⟨s,q,u,v⟩ hs ⟨t,r,u',v'⟩ ht he
    obtain ⟨hs,hw⟩ := mem_sigma.mp hs
    obtain ⟨ht,hw'⟩ := mem_sigma.mp ht
    have hq := (mem_product.mp hw).1
    have hr := (mem_product.mp hw').1
    change (_, u, v) = (_, u', v') at he
    obtain ⟨he, huv⟩ := Prod.mk.inj he
    cases huv
    have hd : m • (s - t) = q - r := by
      rw [smul_sub]
      abel_nf at he ⊢
      linear_combination (norm := abel) he
    have hqr : q = r := by
      by_contra hn
      have := hsep q hq r hr hn
      rw [dist_eq_norm, ← hd] at this
      exact (not_lt_of_ge (hdiam s hs t ht)) this
    subst r
    have hz : m • (s - t) = 0 := by simpa using hd
    have hst : s = t := sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hm)
    subst t
    rfl
  simpa [domain, card_sigma, card_product] using card_le_card_of_injOn encode maps inj

/-- Finitely many translates of radius-1/7 balls cover every unit ball,
with one list of offsets for the whole space. -/
theorem small_ball_cover (p : ℕ) : ∃ F : Finset (V p), ∀ y : V p,
    Metric.ball y 1 ⊆ ⋃ c ∈ F, Metric.ball (y + c) (1 / 7) := by
  classical
  obtain ⟨D, _, hD, hcover⟩ := (isCompact_closedBall (0 : V p) 1).finite_cover_balls
    (show (0 : ℝ) < 1 / 7 by norm_num)
  refine ⟨hD.toFinset, ?_⟩
  intro y s hs
  have hmem : s - y ∈ Metric.closedBall (0 : V p) 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using (Metric.mem_ball.mp hs).le
  obtain ⟨c, hc, hsc⟩ := Set.mem_iUnion₂.mp (hcover hmem)
  apply Set.mem_iUnion₂.mpr
  refine ⟨c, hD.mem_toFinset.mpr hc, ?_⟩
  simpa [Metric.mem_ball, dist_eq_norm, sub_add_eq_sub_sub] using hsc

end HalfBall
