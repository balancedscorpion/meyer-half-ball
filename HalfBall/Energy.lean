module

public import HalfBall.Decomposition
public import HalfBall.LocalCount

@[expose] public section
namespace HalfBall

open Finset
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

private def diffCount (A : Finset G) (d : G) :=
  ((A ×ˢ A).filter fun x => x.1 - x.2 = d).card

private theorem energy_by_differences (A B W : Finset G) (hW : A - A ⊆ W) :
    (∑ d ∈ W, diffCount A d * diffCount B d) = addEnergy A B := by
  classical
  let E := ((A ×ˢ A) ×ˢ (B ×ˢ B)).filter fun x => x.1.1 + x.2.1 = x.1.2 + x.2.2
  let f (x : (G × G) × (G × G)) := x.1.1 - x.1.2
  have hf (x) (hx : x ∈ E) : f x ∈ W := by
    obtain ⟨ha,_⟩ := mem_product.mp (mem_filter.mp hx).1
    exact hW (sub_mem_sub (mem_product.mp ha).1 (mem_product.mp ha).2)
  calc _ = ∑ d ∈ W, (E.filter fun x => f x = d).card := by
         apply sum_congr rfl
         intro d _
         unfold diffCount
         rw [← card_product]
         refine card_bij' (fun x _ => (x.1,x.2.2,x.2.1)) (fun x _ => (x.1,x.2.2,x.2.1))
           ?_ ?_ (by intros; rfl) (by intros; rfl)
         · rintro ⟨⟨a,a'⟩,b,b'⟩ hx
           simp only [E,f,mem_product,mem_filter] at hx ⊢
           obtain ⟨⟨ha,had⟩,⟨hb,hb'⟩,hbd⟩ := hx
           exact ⟨⟨⟨ha,hb',hb⟩,by linear_combination (norm := abel) had - hbd⟩,had⟩
         · rintro ⟨⟨a,a'⟩,b,b'⟩ hx
           simp only [E,f,mem_product,mem_filter] at hx ⊢
           obtain ⟨⟨⟨ha,hb,hb'⟩,he⟩,had⟩ := hx
           exact ⟨⟨ha,had⟩,⟨hb',hb⟩,by linear_combination (norm := abel) had - he⟩
       _ = _ := by rw [sum_card_fiberwise_eq_card_filter, filter_eq_self.mpr hf]; rfl

/-- Cauchy–Schwarz for the two difference multiplicities. -/
theorem mixed_energy_sq (A B : Finset G) :
    addEnergy A B ^ 2 ≤ addEnergy A A * addEnergy B B := by
  let W := (A-A) ∪ (B-B)
  have hA : A-A ⊆ W := subset_union_left
  have hB : B-B ⊆ W := subset_union_right
  have h := sum_mul_sq_le_sq_mul_sq W (diffCount A) (diffCount B)
  simpa only [sq, ← energy_by_differences A B W hA,
    ← energy_by_differences A A W hA, ← energy_by_differences B B W hB] using h

variable {p : ℕ}

/-- Group the last two coordinates by their sum. Each admissible sum
determines its first coordinate in A. -/
theorem reps_sq (A B C : Finset (V p)) (v : V p) :
    (representations A B C v).card ^ 2 ≤ A.card * addEnergy B C := by
  classical
  let W := (B+C).filter fun t => v-t ∈ A
  let r (t : V p) := ((B ×ˢ C).filter fun x => x.1 + x.2 = t).card
  have hw : W.card ≤ A.card := card_le_card_of_injOn (v - ·)
    (fun _ hx => (mem_filter.mp hx).2) sub_right_injective.injOn
  have hr : ∑ t ∈ W, r t = (representations A B C v).card := by
    unfold r
    rw [sum_card_fiberwise_eq_card_filter]
    congr 1
    ext x
    simp only [representations,W,mem_filter,mem_product,sub_add_eq_sub_sub]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,add_mem_add h.1.1 h.1.2,h.2⟩⟩
  have he : ∑ t ∈ W, r t ^ 2 ≤ addEnergy B C := by
    rw [addEnergy_eq_sum_sq']
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
  have hcs := sum_mul_sq_le_sq_mul_sq W (fun _ => (1 : ℕ)) r
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,hr] at hcs
  exact hcs.trans (Nat.mul_le_mul hw he)

/-- The remainder in either of the last two positions costs at most the
fourth root of its energy times the five-fourths power of the site count. -/
theorem reps_fourth (A B C : Finset (V p)) (v : V p) (n : ℕ)
    (ha : A.card ≤ n) (hc : C.card ≤ n) :
    (representations A B C v).card ^ 4 ≤ n ^ 5 * addEnergy B B := calc
  _ = ((representations A B C v).card ^ 2) ^ 2 := by ring
  _ ≤ (A.card * addEnergy B C) ^ 2 := Nat.pow_le_pow_left (reps_sq A B C v) _
  _ = A.card ^ 2 * addEnergy B C ^ 2 := mul_pow ..
  _ ≤ n ^ 2 * (addEnergy B B * n ^ 3) := by
    gcongr
    exact (mixed_energy_sq B C).trans (Nat.mul_le_mul_left _ ((energy_le_cube C).trans (by gcongr)))
  _ = _ := by ring

end HalfBall
