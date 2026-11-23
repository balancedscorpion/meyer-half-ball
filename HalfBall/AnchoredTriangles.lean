module

public import HalfBall.Geometry.Parameters
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Filter Finset MeasureTheory
open scoped Topology InnerProductSpace

private theorem pruning_score {N Λ g D τ H b e z : ℝ} (hN : 0 < N) (hΛ : 0 < Λ)
    (hD : 0 < D) (hb : b*Λ/N ≤ 1/8) (he : e ≤ g*N) (hz : z ≤ H*(τ*N^2))
    (hdeg : g*Λ ≤ D/8) (htri : H*τ*Λ^2 ≤ 1/8) :
    Λ/N/2 ≤ Λ/N - b*(Λ/N)^2 - e*(Λ/N)^2/D - z*(Λ/N)^3 := by
  have hq : 0 < Λ/N := div_pos hΛ hN
  have hb' : b*(Λ/N)^2 ≤ (Λ/N)/8 := by
    have := mul_le_mul_of_nonneg_right hb hq.le
    convert this using 1 <;> ring
  have he' : e*(Λ/N)^2/D ≤ Λ/N/8 := by
    apply (div_le_iff₀ hD).mpr
    calc _ ≤ g*N*(Λ/N)^2 := by gcongr
         _ = (g*Λ)*(Λ/N) := by field_simp
         _ ≤ D/8*(Λ/N) := by gcongr
         _ = _ := by ring
  have hz' : z*(Λ/N)^3 ≤ Λ/N/8 := calc
    _ ≤ H*(τ*N^2)*(Λ/N)^3 := by gcongr
    _ = (H*τ*Λ^2)*(Λ/N) := by field_simp
    _ ≤ 1/8*(Λ/N) := by gcongr
    _ = _ := by ring
  linarith

/-- Lemma A.4. A positive quadratic number of exact offset triples is forced
at every fixed anchor eventually, uniformly in the choice of partition.
The constants preceding φ and X₀ depend only on dimension and the two
bounds. The anchor-specific isolation radius determines only the mesh and
the threshold in the final eventuality. -/
theorem anchored_triangle_bound {p : ℕ} (hp : 0 < p) {B : Set (V p)} (hB : LocallyFiniteSites B)
    {η : V p} (hη : ‖η‖ = 1) (hpatch : OrderedPatchBound B) {S : ℕ → ℝ}
    (hS : HalfBallCount B η S) : AnchoredTriangleBound hB η S := by
  classical
  obtain ⟨a,ha,patch⟩ := hpatch
  obtain ⟨C,hC,hsize⟩ := scale_count_bound hB hp hS
  let g := 2*(4:ℝ)^p*C
  let H := ((4:ℝ)^p)^2
  have hg : 0 < g := by dsimp [g]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨k,hk⟩ := exists_nat_gt (128*(g+1)*(4:ℝ)^p*a)
  let D := k*(2^k+1)+1
  have hD : 0 < D := Nat.succ_pos _
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  let Λ := (D:ℝ)/(8*(g+1))
  have hΛ : 0 < Λ := by dsimp [Λ]; positivity
  let τ := 1/(8*H*Λ^2)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hbudget : 16*D*(4:ℝ)^p*a < k*Λ := by
    unfold Λ
    rw [← mul_div_assoc,lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right hk hD']
  refine ⟨τ,hτ,?_⟩
  intro φ hφ X₀ hX₀ hzero s hs
  obtain ⟨r,hr,_,hisol⟩ := anchor_isolation hB s
  let d := r/(4*(Real.sqrt p+1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hsep : Real.sqrt p*(2*d) < r := by
    dsimp [d]
    field_simp
    nlinarith [Real.sqrt_nonneg (p:ℝ),mul_nonneg (Real.sqrt_nonneg (p:ℝ)) hr.le]
  let J : ℕ := 2*(2*⌈(2*d+1)/d⌉₊+2)^p
  have hJ : (0 : ℝ) < J := by dsimp [J]; positivity
  let R j := S (φ j)
  let w j := R j / (3*Real.sqrt p)
  let N j := (w j)^p
  have hRlim : Tendsto R atTop atTop := hS.2.1.comp hφ.tendsto_atTop
  have hwlim : Tendsto w atTop atTop := hRlim.atTop_div_const (by positivity)
  have hNlim : Tendsto N atTop atTop := (tendsto_pow_atTop hp.ne').comp hwlim
  have hbadlim : Tendsto (fun j => ((packing (X₀ j)).card : ℝ) / N j * (J*Λ)) atTop (𝓝 0) := by
    change Tendsto (fun j => ((packing (X₀ j)).card : ℝ)/N j) atTop (𝓝 0) at hzero
    simpa only [zero_mul] using hzero.mul_const (J*Λ)
  filter_upwards [hφ.tendsto_atTop.eventually hsize, hRlim.eventually_ge_atTop (2*‖s‖),
    hwlim.eventually_ge_atTop (2*d),hNlim.eventually_ge_atTop Λ,
    hbadlim.eventually_lt_const (show (0:ℝ) < 1/8 by norm_num)] with j hsizej hsR hwj hNj hbadj
  let X := sites hB η (R j)
  let X₁ := X \ X₀ j
  let F := anchoredOffsets X₁ s η (R j)
  let F₀ := anchoredOffsets (X₀ j) s η (R j)
  change τ*N j^2 < ((triples F F F 0).card : ℝ)
  by_contra! hfew
  have hR : 0 < R j := hS.1 _
  have hw : 0 < w j := by dsimp [w]; positivity
  have hN : 0 < N j := by dsimp [N]; positivity
  obtain ⟨m,hm,hm'⟩ := coarse_mesh hd hwj
  obtain ⟨n,hn,hheight,hgap⟩ := choose_fine_mesh hB s η hd F
  let t := d/n
  have ht : 0 < t := by dsimp [t]; positivity
  let G := fineGraph (m*n) t F (anchored_symmetric _ _ _ _)
  let bad (v : Grid p (m*n)) := coarsePartners m d F₀ (coarse hn v)
  have hfar (Y : Finset (V p)) (hY : Y ⊆ X) : ∀ h ∈ anchoredOffsets Y s η (R j),
      Real.sqrt p*(2*d) < ‖h‖ := by
    intro h hh
    obtain ⟨x,hx,hne,_,_,h | h⟩ := mem_anchoredOffsets.mp hh
    all_goals
      have hb := ((mem_sites ..).mp (hY hx)).1
      simpa only [h,norm_neg] using hsep.trans_le (hisol x hb hne)
  let q := Λ/N j
  have hq : q ∈ Set.Icc 0 1 := ⟨(div_pos hΛ hN).le,(div_le_one hN).mpr hNj⟩
  obtain ⟨I,hI,hbad,hcount⟩ := sample_independent G (coarse hn) bad
    (fun v => coarse_no_self hd F₀ (hfar _ (hX₀ j)) _) (fine_crosses_coarse hd hn rfl F _
      (hfar _ sdiff_subset)) q hq k D hD (by dsimp [D]; omega)
  have hvol := ordered_cells_bound hB hp ha patch hs hη hd hR (by linarith : ‖s‖ ≤ R j/2) hn hm
    (fun b hb hne => lt_of_le_of_lt (by
      have ht' : d/(n:ℝ) ≤ d := div_le_self hd.le (by exact_mod_cast hn)
      exact mul_le_mul_of_nonneg_left (show d/(n:ℝ) ≤ 2*d by linarith) (by positivity))
      (hsep.trans_le (hisol b hb hne))) hheight (X₀ j) I hI hbad
  have hscore (v : Grid p (m*n)) : q/2 ≤ q - (bad v).card*q^2 - (G.degree v)*q^2/D -
      (trianglesAt G v).card*q^3 := by
    have hb : (bad v).card ≤ (packing (X₀ j)).card*J := coarse_partner_bound m hd _ _ _ _ _
    have hdeg := fine_degree (m*n) ht F (anchored_symmetric _ _ _ _) v
    have hf := (anchored_card X₁ s η (R j)).trans (Nat.mul_le_mul_left _ (card_le_card sdiff_subset))
    have he : (G.degree v : ℝ) ≤ (2*X.card)*((4:ℝ)^p) := by
      exact_mod_cast hdeg.trans (Nat.mul_le_mul_right _ hf)
    have hz := fine_triangles (m*n) ht F (anchored_symmetric _ _ _ _) v hgap
    apply pruning_score hN hΛ hD' (g := g) (τ := τ) (H := H)
    · have hb' : ((bad v).card : ℝ) ≤ (packing (X₀ j)).card*(J:ℝ) := by exact_mod_cast hb
      calc _ ≤ ((packing (X₀ j)).card*J:ℝ)*Λ/N j := by gcongr
           _ = _ := by ring
           _ ≤ _ := hbadj.le
    · refine he.trans ?_
      change 2*(X.card:ℝ)*4^p ≤ 2*4^p*C*N j
      have hx : (X.card:ℝ) ≤ C*N j := hsizej
      nlinarith [mul_le_mul_of_nonneg_right hx (show (0:ℝ) ≤ 2*4^p by positivity)]
    · have hz' : ((trianglesAt G v).card:ℝ) ≤ (triples F F F 0).card*H := by dsimp only [H]; exact_mod_cast hz
      exact hz'.trans (by rw [mul_comm H]; gcongr)
    · unfold Λ; field_simp; linarith
    · unfold τ; field_simp; rfl
  have htotal := sum_le_sum (s := univ) (fun v _ => hscore v)
  simp only [sum_const,card_univ,nsmul_eq_mul] at htotal
  exact hbudget.not_ge (volume_accounting p m n k D hd hw hΛ hn hm' I
    ((mul_le_mul_of_nonneg_left htotal (by positivity)).trans hcount) hvol)

end HalfBall
