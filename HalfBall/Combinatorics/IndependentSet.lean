module

public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic

@[expose] public section
namespace HalfBall

open Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
private theorem subfamilies_total_size (S : Finset α) :
    2 * (∑ T ∈ S.powerset, T.card) = S.card * 2 ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    rw [sum_powerset_insert hx,card_insert_of_notMem hx]
    have he : ∑ T ∈ S.powerset, (insert x T).card = ∑ T ∈ S.powerset, (T.card + 1) := by
      apply sum_congr rfl
      intro T ht
      exact card_insert_of_notMem (fun h => hx (mem_powerset.mp ht h))
    rw [he,sum_add_distrib]
    simp only [sum_const, nsmul_eq_mul, mul_one, card_powerset, pow_succ]
    nlinarith

variable (G : SimpleGraph α) [DecidableRel G.Adj]

private def Independent (S : Finset α) : Prop := ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y

private noncomputable def family : Finset (Finset α) := by
  classical
  exact univ.filter (Independent G)

private def outside (v : α) (S : Finset α) := S \ insert v (G.neighborFinset v)

private noncomputable def unblocked (v : α) (J : Finset α) := by
  classical
  exact (G.neighborFinset v).filter (fun w => ∀ z ∈ J, ¬ G.Adj w z)

omit [DecidableEq α] [DecidableRel G.Adj] in
private theorem in_family {S : Finset α} : S ∈ family G ↔ Independent G S := by
  classical
  simp [family]

private theorem extensions (htri : G.CliqueFree 3) (v : α) (J : Finset α)
    (hJ : Independent G J) (hfar : ∀ x ∈ J, x ∉ insert v (G.neighborFinset v)) :
    ((family G).filter (fun I => outside G v I = J)) =
      insert (insert v J) (((unblocked G v J).powerset).image (J ∪ ·)) := by
  classical
  let N := G.neighborFinset v
  let Z := unblocked G v J
  have hfree {w} (hw : w ∈ Z) : w ∈ N ∧ ∀ z ∈ J, ¬ G.Adj w z := mem_filter.mp hw
  have hind {x y} (hx : x ∈ N) (hy : y ∈ N) : ¬ G.Adj x y := by
    by_cases he : x=y
    · subst y; exact G.loopless.irrefl _
    · exact G.isIndepSet_neighborSet_of_triangleFree htri v
        ((G.mem_neighborFinset v x).mp hx) ((G.mem_neighborFinset v y).mp hy) he
  ext I
  simp only [mem_filter,in_family,mem_insert,mem_image,mem_powerset]
  constructor
  · rintro ⟨hi,ho⟩
    by_cases hv : v ∈ I
    · left
      ext x
      simp only [← ho,outside,mem_insert,mem_sdiff,not_or]
      by_cases h : x=v
      · simp [h,hv]
      · simp only [h,false_or,not_false_eq_true,true_and]
        exact ⟨fun hx => ⟨hx,fun hn => hi v hv x hx ((G.mem_neighborFinset v x).mp hn)⟩,And.left⟩
    · right
      refine ⟨I ∩ N,?_,?_⟩
      · intro w hw
        obtain ⟨hw,hn⟩ := mem_inter.mp hw
        exact mem_filter.mpr ⟨hn,fun z hz => hi w hw z (mem_sdiff.mp (ho ▸ hz)).1⟩
      · ext x
        simp only [← ho,outside,mem_sdiff,mem_insert,not_or,mem_union,mem_inter]
        by_cases hx : x ∈ N <;> by_cases hxv : x=v <;> simp_all [N]
  · rintro (rfl | ⟨T,hT,rfl⟩)
    · constructor
      · intro x hx y hy
        rcases mem_insert.mp hx with hxv | hx <;> rcases mem_insert.mp hy with hyv | hy
        all_goals try subst x
        all_goals try subst y
        · exact G.loopless.irrefl _
        · exact fun e => hfar _ hy (mem_insert_of_mem ((G.mem_neighborFinset ..).mpr e))
        · exact fun e => hfar _ hx (mem_insert_of_mem ((G.mem_neighborFinset ..).mpr e.symm))
        · exact hJ _ hx _ hy
      · ext x
        simp only [outside,mem_sdiff,mem_insert,not_or]
        constructor
        · rintro ⟨h,hn,_⟩; exact h.resolve_left hn
        · intro hx
          exact ⟨Or.inr hx,fun he => hfar x hx (mem_insert.mpr (Or.inl he)),
            fun hn => hfar x hx (mem_insert_of_mem hn)⟩
    · constructor
      · intro x hx y hy
        rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
        · exact hJ _ hx _ hy
        · exact fun e => (hfree (hT hy)).2 _ hx e.symm
        · exact (hfree (hT hx)).2 _ hy
        · exact hind (hfree (hT hx)).1 (hfree (hT hy)).1
      · ext x
        simp only [outside,mem_sdiff,mem_union]
        constructor
        · rintro ⟨h,hn⟩
          exact h.resolve_right (fun hx => hn (mem_insert_of_mem (hfree (hT hx)).1))
        · intro hx; exact ⟨Or.inl hx,hfar _ hx⟩

private def charge (D : ℕ) (v : α) (S : Finset α) :=
  (if v ∈ S then D else 0) + (S ∩ G.neighborFinset v).card

private theorem extension_charge (htri : G.CliqueFree 3) (k D : ℕ)
    (hD : k * (2^k + 1) ≤ 4*D) (v : α) (J : Finset α)
    (hJ : Independent G J) (hfar : ∀ x ∈ J, x ∉ insert v (G.neighborFinset v)) :
    let F := (family G).filter fun I => outside G v I = J
    k * F.card ≤ 4 * ∑ S ∈ F, charge G D v S := by
  classical
  dsimp only
  rw [extensions G htri v J hJ hfar]
  let Z := unblocked G v J
  let N := G.neighborFinset v
  have hnear {x} (h : x ∈ Z) : x ∈ N := (mem_filter.mp h).1
  have hvJ : v ∉ J := fun h => hfar _ h (mem_insert_self _ _)
  have hvN : v ∉ N := by simp [N]
  have hJn {x} (h : x ∈ J) : x ∉ N := fun hn => hfar _ h (mem_insert_of_mem hn)
  have recover (T : Finset α) (hT : T ⊆ Z) : (J ∪ T) ∩ N = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨hu,hn⟩ := mem_inter.mp hx
      exact (mem_union.mp hu).resolve_left (fun hj => hJn hj hn)
    · intro hx
      exact mem_inter.mpr ⟨mem_union_right _ hx,hnear (hT hx)⟩
  have hinj : Set.InjOn (J ∪ ·) (↑Z.powerset) := by
    intro T hT T' hT' he
    change J ∪ T = J ∪ T' at he
    rw [← recover T (mem_powerset.mp hT), ← recover T' (mem_powerset.mp hT'), he]
  have hvT (T : Finset α) (hT : T ⊆ Z) : v ∉ J ∪ T := fun hv =>
    hvN (hnear (hT ((mem_union.mp hv).resolve_left hvJ)))
  have hnew : insert v J ∉ Z.powerset.image (J ∪ ·) := by
    rintro h
    obtain ⟨T,hT,he⟩ := mem_image.mp h
    exact hvT T (mem_powerset.mp hT) (he ▸ mem_insert_self _ _)
  have hb : charge G D v (insert v J) = D := by
    have h0 : insert v J ∩ N = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hx,hn⟩ := mem_inter.mp hx
      rcases mem_insert.mp hx with rfl | hj
      · exact hvN hn
      · exact hJn hj hn
    change (if v ∈ insert v J then D else 0) + (insert v J ∩ N).card = D
    rw [h0]; simp
  have ht (T : Finset α) (hT : T ∈ Z.powerset) : charge G D v (J ∪ T) = T.card := by
    have hz := mem_powerset.mp hT
    change (if v ∈ J ∪ T then D else 0) + ((J ∪ T) ∩ N).card = T.card
    rw [recover T hz,ite_eq_right (hvT T hz),zero_add]
  rw [card_insert_of_notMem hnew, card_image_of_injOn hinj, card_powerset,
    sum_insert hnew, hb,sum_image hinj,sum_congr rfl ht]
  by_cases hz : Z.card ≤ k
  · have hm : 2 ^ Z.card ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hz
    exact (Nat.mul_le_mul_left k (Nat.add_le_add_right hm 1)).trans (by omega)
  · have hh := subfamilies_total_size Z
    have hpow : 1 ≤ 2^Z.card := Nat.one_le_two_pow
    have h1 := Nat.mul_le_mul_right (2^Z.card) (Nat.le_of_not_ge hz)
    have h2 := Nat.mul_le_mul_left k hpow
    nlinarith

private theorem vertex_charge (htri : G.CliqueFree 3) (k D : ℕ)
    (hD : k*(2^k+1) ≤ 4*D) (v : α) :
    k * (family G).card ≤ 4 * ∑ S ∈ family G, charge G D v S := by
  classical
  let f := outside G v
  let J := (family G).image f
  have hm : Set.MapsTo f (↑(family G)) (↑J) := fun _ hs => mem_image_of_mem _ hs
  rw [card_eq_sum_card_fiberwise hm,mul_sum,← sum_fiberwise_of_maps_to hm (charge G D v),
    mul_sum]
  apply sum_le_sum
  intro j hj
  obtain ⟨I,hI,rfl⟩ := mem_image.mp hj
  exact extension_charge G htri k D hD v _ (fun x hx y hy =>
    (in_family G).mp hI x (mem_sdiff.mp hx).1 y (mem_sdiff.mp hy).1)
    (fun _ hx => (mem_sdiff.mp hx).2)

private theorem set_charge (D : ℕ) (hd : ∀ v, G.degree v ≤ D) (I : Finset α) :
    ∑ v, charge G D v I ≤ 2 * D * I.card := by
  classical
  have hcnt (v : α) : (I ∩ G.neighborFinset v).card =
      ∑ w ∈ I, if G.Adj w v then 1 else 0 := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    congr 1
    ext w
    simp [G.adj_comm]
  simp only [charge,sum_add_distrib,hcnt]
  rw [sum_comm (s := univ) (t := I)]
  have hins : (∑ v : α, if v ∈ I then D else 0) = I.card * D := by
    rw [← sum_filter]; simp
  rw [hins]
  have hcount (w : α) : (∑ v : α, if G.Adj w v then 1 else 0) = G.degree w := by
    rw [sum_boole, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    rfl
  simp_rw [hcount]
  have hle := sum_le_sum (s := I) (fun v _ => hd v)
  simp only [sum_const,nsmul_eq_mul] at hle
  nlinarith

/-- A triangle-free finite graph of degree at most D has an independent
set of size at least k|V|/(8D) when k(2^k+1) ≤ 4D. -/
theorem triangle_free_independent_set (htri : G.CliqueFree 3) (k D : ℕ)
    (hD : k*(2^k+1) ≤ 4*D) (hd : ∀ v, G.degree v ≤ D) :
    ∃ I : Finset α, G.IsIndepSet (↑I) ∧ k*Fintype.card α ≤ 8*D*I.card := by
  classical
  have hempty : (∅ : Finset α) ∈ family G := (in_family G).mpr (by simp [Independent])
  obtain ⟨I,hI,hmax⟩ := (family G).exists_max_image card ⟨∅,hempty⟩
  refine ⟨I,fun _ hx _ hy _ => (in_family G).mp hI _ hx _ hy,?_⟩
  have hlow := sum_le_sum (s := univ) (fun v _ => vertex_charge G htri k D hD v)
  simp only [sum_const,card_univ,nsmul_eq_mul,← mul_sum] at hlow
  rw [sum_comm] at hlow
  have hup := sum_le_sum (s := family G) (fun S hS =>
    (set_charge G D hd S).trans (Nat.mul_le_mul_left _ (hmax S hS)))
  simp only [sum_const,nsmul_eq_mul] at hup
  have hprod := hlow.trans (Nat.mul_le_mul_left 4 hup)
  apply Nat.le_of_mul_le_mul_right (c := (family G).card) _ (card_pos.mpr ⟨∅,hempty⟩)
  nlinarith

end HalfBall
