module
public import HalfBall.Classification.PhaseDifference
import Mathlib.Tactic

public section
noncomputable section
namespace HalfBall.Weights
open HalfBall.Classification MeyerGeneralProblem.LevOlevskii Set Metric FourierTransform MeasureTheory Filter Finset
open scoped FourierTransform Convolution Topology

private theorem zero_cardinals {p M} {δ : ℝ} (hd : 0 < δ) :
    ∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧ ∀ E : Set (V p), LocallyFiniteSites E → BallCap E M →
      (∀ x ∈ E, x ≠ 0 → δ ≤ dist x 0) →
      ∃ φ : SchwartzMap (V p) ℂ, Function.support φ ⊆ closedBall 0 R ∧ (∀ y, ‖φ y‖ ≤ C) ∧
        (𝓕 φ) 0 = 1 ∧ ∀ x ∈ E, x ≠ 0 → (𝓕 φ) x = 0 := by
  classical
  let d := min 1 δ
  obtain ⟨r,K,hr,hK,hsep⟩ := finite_separated_interpolation_at_scale p (lt_min zero_lt_one hd : 0 < d)
  obtain ⟨t,ht,htest⟩ := bandlimited_isolation_at_point p (η := 1) zero_lt_one
  obtain ⟨β,hβ,hβ₀,_⟩ := htest ∅ (by simp) 0
  let C := K^M
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨U,hU,L,hUL⟩ := inverse_envelope_bounds (𝓕 β) hC
  let D := (M:ℝ)*r+t
  have hcb : HasCompactSupport (β : V p → ℂ) := HasCompactSupport.intro (isCompact_closedBall _ _) fun _ h => not_not.mp (mt (@hβ _) h)
  refine ⟨t+D,(∫ x, ‖β x‖)*U,by dsimp [D]; positivity,
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) hU,fun E hE hcap hiso => ?_⟩
  obtain ⟨F,hF,hsepF⟩ := separated_classes_of_ballCap hcap
  have hFE i : F i ⊆ E := fun x hx => hF ▸ mem_iUnion.mpr ⟨i,hx⟩
  let window (n : ℕ) := (hE _ (isCompact_closedBall 0 (n:ℝ))).toFinset
  let G n (i : Fin M) := insert 0 ((window n).filter (fun x => x ∈ F i))
  have hG n i : (G n i : Set (V p)).Pairwise (fun x y => d ≤ dist x y) := by
    rw [show (G n i : Set (V p)) = insert 0 (((window n).filter (fun x => x ∈ F i) : Finset _) : Set _) from coe_insert ..,pairwise_insert]
    refine ⟨fun x hx y hy hn => (min_le_left ..).trans (hsepF i (mem_filter.mp hx).2 (mem_filter.mp hy).2 hn),?_⟩
    intro y hy hn
    have hh := (min_le_right 1 δ).trans (hiso y (hFE i (mem_filter.mp hy).2) (by grind))
    exact ⟨dist_comm y 0 ▸ hh,hh⟩
  choose q hqB hqN hqV using fun n i => hsep (G n i) (hG n i)
    (fun z => if z.val = 0 then (1:ℂ) else 0) (fun z => by split_ifs <;> simp)
  let f n (x : V p) := ∏ i, q n i x
  have hbnd (n) (I : Finset (Fin M)) : Bandwidth (I.card*r) (fun x => ∏ i ∈ I, q n i x) := by
    induction I using Finset.induction_on with
    | empty => simpa using (Bandwidth.const (p := p) 1)
    | insert i I hi ih =>
      simpa [hi,add_mul,add_comm] using (hqB n i).mul ih
  have hband n : Bandwidth ((M:ℝ)*r) (f n) := by simpa [f] using hbnd n univ
  have hf n x : ‖f n x‖ ≤ C := by
    have bound (I : Finset (Fin M)) : ∏ i ∈ I, ‖q n i x‖ ≤ K^I.card := by
      induction I using Finset.induction_on with
      | empty => simp
      | insert i I hi ih =>
        rw [prod_insert hi,card_insert_of_notMem hi,pow_succ']
        exact mul_le_mul (hqN n i x) ih (prod_nonneg fun _ _ => norm_nonneg _) (by linarith)
    simpa [f,C,norm_prod] using bound univ
  choose ψ hs hv using fun n => hband n t β hβ
  have hp n x : ‖(𝓕 (ψ n)) x‖ ≤ C*‖(𝓕 β) x‖ := by rw [hv,norm_mul]; exact mul_le_mul_of_nonneg_right (hf n x) (norm_nonneg _)
  obtain ⟨g,hg,hgs,hgN,θ,hθ,hlim⟩ := compact_window_subsequence ψ hs (fun n => (hUL _ (hp n)).1) (fun n => (hUL _ (hp n)).2)
  have hcg : HasCompactSupport g := HasCompactSupport.intro (isCompact_closedBall _ _) fun _ h => not_not.mp (mt (@hgs _) h)
  have hgz : 𝓕 g 0 = 1 := by
    apply tendsto_nhds_unique (hlim 0) (tendsto_const_nhds.congr (fun n => ?_))
    rw [hv,hβ₀,mul_one]; symm
    apply Finset.prod_eq_one; intro i _
    simpa using hqV (θ n) i ⟨0,mem_insert_self ..⟩
  have hgo x (hx : x ∈ E) (hn : x ≠ 0) : 𝓕 g x = 0 := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hF ▸ hx)
    obtain ⟨j,hj⟩ := exists_nat_gt ‖x‖
    apply tendsto_nhds_unique (hlim x) (tendsto_const_nhds.congr' ?_)
    filter_upwards [hθ.tendsto_atTop.eventually_ge_atTop j] with n hjn
    have hmem : x ∈ window (θ n) := (Set.Finite.mem_toFinset _).mpr ⟨hx,by simpa using hj.le.trans (show (j:ℝ) ≤ θ n by exact_mod_cast hjn)⟩
    have hq : q (θ n) i x = 0 := by
      simpa [hn] using hqV (θ n) i ⟨x,mem_insert_of_mem (mem_filter.mpr ⟨hmem,hi⟩)⟩
    rw [hv,show f (θ n) x = 0 from Finset.prod_eq_zero (mem_univ i) hq,zero_mul]
  let Lr := ContinuousLinearMap.mul ℝ ℂ
  let Gf := (β : V p → ℂ) ⋆[Lr] g
  have hcf : HasCompactSupport Gf := hcb.convolution Lr hcg
  let φ := hcf.toSchwartzMap (hcb.contDiff_convolution_left Lr (β.smooth _) hg.locallyIntegrable)
  have hval x : (𝓕 φ) x = (𝓕 β) x * 𝓕 g x := by
    change 𝓕 ((β : V p → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x = _
    exact Real.fourier_mul_convolution_eq β.integrable (hg.integrable_of_hasCompactSupport hcg) _
  refine ⟨φ,?_,fun y => ?_,by simp [hval,hgz,hβ₀],fun x hx hn => by simp [hval,hgo x hx hn]⟩
  · intro y hy
    have hh : y ∈ Function.support Gf := hy
    obtain ⟨v,hv,w,hw,rfl⟩ := support_convolution_subset Lr hh
    simpa using (norm_add_le v w).trans (add_le_add (show ‖v‖ ≤ t by simpa using hβ hv) (show ‖w‖ ≤ D by simpa using hgs hw))
  · change ‖∫ z, β z*g (y-z)‖ ≤ _
    rw [← integral_mul_const]
    apply norm_integral_le_of_norm_le (β.integrable.norm.mul_const U)
    exact ae_of_all _ fun z => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hgN _) (norm_nonneg _)

/-- Actual atomic coefficients are uniformly bounded at all sites whose
distance to the other sites exceeds a prescribed positive threshold. -/
theorem bounded_at_isolated_sites {p M} {μ : TemperedDistribution (V p) ℂ} {A B : Set (V p)}
    {a : A → ℂ} {b : B → ℂ} (ha : HasLocallyAtomicExpansion μ A a) (hb : HasLocallyAtomicExpansion (𝓕 μ) B b)
    (hA : LocallyFiniteSites A) (hB : LocallyFiniteSites B) (cap : BallCap A M) {δ : ℝ} (hd : 0 < δ) :
    ∃ C : ℝ, ∀ x : A, (∀ y ∈ A, y ≠ x.val → δ ≤ dist y x.val) → ‖a x‖ ≤ C := by
  classical
  obtain ⟨R,C,_,_,hcard⟩ := zero_cardinals (p := p) (M := M) hd
  let F : Finset B := (hB _ (isCompact_closedBall 0 R)).toFinset.preimage Subtype.val Subtype.val_injective.injOn
  have hF (z : B) : z ∈ F ↔ ‖z.val‖ ≤ R := by simp [F,mem_closedBall]
  refine ⟨(∑ z ∈ F,‖b z‖)*C,fun x hδ => ?_⟩
  let E := {y : V p | y+x.val ∈ A}
  have hf : LocallyFiniteSites E := by
    intro K hK
    apply ((hA _ (hK.image (Homeomorph.addRight x.val).continuous)).image (fun z => z-x.val)).subset
    rintro y ⟨hy,hyK⟩
    exact ⟨y+x.val,⟨hy,⟨y,hyK,rfl⟩⟩,add_sub_cancel_right ..⟩
  have hcap : BallCap E M := by
    intro y T hT
    let e : V p ↪ V p := ⟨fun y => y+x.val,add_left_injective _⟩
    have hh := cap (y+x.val) (T.map e) (by
      intro z hz
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hz
      exact ⟨(hT hv).1,by simpa [e,mem_ball] using (hT hv).2⟩)
    simpa using hh
  obtain ⟨φ,hs,hn,hz,hothers⟩ := hcard E hf hcap (fun y hy hne => by
    simpa [dist_eq_norm] using hδ (y+x.val) hy (by simpa using hne))
  let ψ := 𝓕⁻ ((SchwartzMap.compSubConstCLM ℂ x.val) (𝓕 φ))
  have hval (y : V p) : ψ y = (frequencyPhase (-x.val) (-y) : ℂ)*φ y := by
    have hh := fourier_test_add (𝓕 φ) (-x.val) (-y)
    have hφ := congrArg (fun g : SchwartzMap (V p) ℂ => g y) (fourierInv_fourier_eq (F := SchwartzMap (V p) ℂ) φ)
    change (𝓕 (𝓕 φ)) (-y) = φ y at hφ
    change (𝓕 ((SchwartzMap.compSubConstCLM ℂ x.val) (𝓕 φ))) (-y) = _
    simpa only [neg_neg,hφ] using hh
  have hsf : Function.support ψ ⊆ closedBall 0 R := fun y hy => hs (fun h => hy (by simp [hval,h]))
  have hc : HasCompactSupport (ψ : V p → ℂ) := HasCompactSupport.intro (isCompact_closedBall _ _) fun _ h => not_not.mp (mt (@hsf _) h)
  have hv (y : V p) : (𝓕 ψ) y = (𝓕 φ) (y-x.val) := by simp [ψ,SchwartzMap.compSubConstCLM_apply]
  have hvx := evaluate_isolated_site ha.2 x (𝓕 ψ) (fun z hn => by
    rw [hv]
    exact hothers _ (show z.val-x.val ∈ E by simp [E]) (sub_ne_zero.mpr (fun h => hn (Subtype.ext h))))
  have hvx' : (𝓕 μ) ψ = a x := by simpa [TemperedDistribution.fourier_apply,hv,hz] using hvx
  have hsum := (hb.2 ψ hc).unique (hasSum_sum_of_ne_finset_zero (s := F) (fun z hout => by
    have hzero : ψ z = 0 := by by_contra h; exact hout ((hF _).mpr (by simpa using hsf h))
    rw [hzero,mul_zero]))
  rw [← hvx',hsum,sum_mul]
  apply (norm_sum_le ..).trans (sum_le_sum fun z _ => ?_)
  rw [norm_mul,hval,norm_mul,Circle.norm_coe,one_mul]
  exact mul_le_mul_of_nonneg_left (hn _) (norm_nonneg _)

end HalfBall.Weights
