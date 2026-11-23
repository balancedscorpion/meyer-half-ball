module

public import HalfBall.Energy

@[expose] public section
namespace HalfBall

open Finset
open scoped Pointwise
variable {p : ℕ}

noncomputable def triples (A B C : Finset (V p)) (t : V p) :=
  (A ×ˢ (B ×ˢ C)).filter fun x => x.1 + x.2.1 + x.2.2 = t

theorem card_triples (A B C : Finset (V p)) (t : V p) :
    (triples A B C t).card = (representations A B C t).card := by
  classical
  refine card_bij' (fun x _ => x.2) (fun x _ => (t-x.1-x.2,x)) ?_ ?_ ?_ (by intros; rfl)
  · rintro ⟨a,b,c⟩ h
    obtain ⟨hab,h⟩ := mem_filter.mp h
    obtain ⟨ha,hbc⟩ := mem_product.mp hab
    change a+b+c=t at h
    have he : t-b-c = a := by rw [← h]; abel
    exact mem_filter.mpr ⟨hbc,he ▸ ha⟩
  · rintro ⟨b,c⟩ h
    obtain ⟨hbc,ha⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_product.mpr ⟨ha,hbc⟩,by change t-b-c+b+c = t; abel⟩
  · rintro ⟨a,b,c⟩ h
    have he := (mem_filter.mp h).2
    change a + b + c = t at he
    simp [← he]; abel

theorem card_triples_swap₁ (A B C : Finset (V p)) (t : V p) :
    (triples A B C t).card = (triples B A C t).card := by
  classical
  refine card_bij' (fun x _ => (x.2.1,x.1,x.2.2)) (fun x _ => (x.2.1,x.1,x.2.2))
    ?_ ?_ (by intros; rfl) (by intros; rfl) <;>
    rintro ⟨a,b,c⟩ h <;> simpa [triples, add_comm b a, and_left_comm] using h

theorem card_triples_swap₂ (A B C : Finset (V p)) (t : V p) :
    (triples A B C t).card = (triples A C B t).card := by
  classical
  refine card_bij' (fun x _ => (x.1,x.2.2,x.2.1)) (fun x _ => (x.1,x.2.2,x.2.1))
    ?_ ?_ (by intros; rfl) (by intros; rfl) <;>
    rintro ⟨a,b,c⟩ h <;> simpa [triples,add_right_comm a b c, and_comm] using h

theorem energy_signed (b : Bool) (U : Finset (V p)) :
    addEnergy (signed b U) (signed b U) = addEnergy U U := by
  classical
  cases b
  · rfl
  · unfold addEnergy
    simp only [signed, ite_true]
    refine card_bij' (fun x _ => ((-x.1.1,-x.1.2),-x.2.1,-x.2.2))
      (fun x _ => ((-x.1.1,-x.1.2),-x.2.1,-x.2.2)) ?_ ?_ (by simp) (by simp)
    all_goals
      rintro ⟨⟨a,b⟩,c,d⟩ h
      simpa only [mem_product, mem_filter, mem_neg', neg_neg, Prod.fst, Prod.snd, ← neg_add, neg_inj] using h

theorem signed_card (b : Bool) (A : Finset (V p)) : (signed b A).card = A.card := by
  cases b <;> simp [signed]

def shift (s : V p) (b : Bool) (x : V p) := x - signValue b • s

/-- Store offsets as actual signed displacements, erasing repeated values. -/
noncomputable def offsets (s : V p) (b : Bool) (Y : Finset (V p)) :=
  (signed b Y).image (shift s b)

theorem translated_triples (s : V p) (a b c : Bool) (A B C : Finset (V p)) :
    (triples (offsets s a A) (offsets s b B) (offsets s c C) 0).card =
      (triples (signed a A) (signed b B) (signed c C)
        ((signValue a + signValue b + signValue c) • s)).card := by
  classical
  symm
  refine card_bij' (fun x _ => (shift s a x.1, shift s b x.2.1, shift s c x.2.2))
    (fun x _ => (x.1 + signValue a • s, x.2.1 + signValue b • s, x.2.2 + signValue c • s))
    ?_ ?_ (by simp [shift]) (by simp [shift])
  · rintro ⟨x,y,z⟩ h
    obtain ⟨hm,he⟩ := mem_filter.mp h
    obtain ⟨hx,hyz⟩ := mem_product.mp hm
    obtain ⟨hy,hz⟩ := mem_product.mp hyz
    refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_image_of_mem _ hx,
      mem_product.mpr ⟨mem_image_of_mem _ hy, mem_image_of_mem _ hz⟩⟩, ?_⟩
    change x + y + z = _ at he
    change shift s a x + shift s b y + shift s c z = 0
    simp only [add_smul] at he
    unfold shift
    linear_combination (norm := abel) he
  · rintro ⟨x,y,z⟩ h
    obtain ⟨hm,he⟩ := mem_filter.mp h
    obtain ⟨hx,hyz⟩ := mem_product.mp hm
    obtain ⟨hy,hz⟩ := mem_product.mp hyz
    obtain ⟨x',hx',rfl⟩ := mem_image.mp hx
    obtain ⟨y',hy',rfl⟩ := mem_image.mp hy
    obtain ⟨z',hz',rfl⟩ := mem_image.mp hz
    simp only [shift, sub_add_cancel] at *
    refine mem_filter.mpr ⟨mem_product.mpr ⟨hx',mem_product.mpr ⟨hy',hz'⟩⟩, ?_⟩
    simp only [add_smul] at *
    linear_combination (norm := abel) he

end HalfBall
