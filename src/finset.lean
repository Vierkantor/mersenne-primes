import algebra.big_operators
import data.finset
import data.nat.basic
import logic.basic
import tactic.find
import tactic.linarith
import tactic.ring

import nat

open function(uncurry)

/- TODO: move these to a better place -/
section helpers
universes u1 u2 u3
variables {α : Type u1} {β : Type u2} {γ : Type u3}
@[simp]
lemma uncurry_prod_mk {a : α} {b : β} {f : α → β → γ} : uncurry f (prod.mk a b) = f a b := by unfold uncurry

@[simp]
lemma multiset.map_empty {f : α → β} : multiset.map f (∅ : finset α).val = 0 := by simp
@[simp]
lemma multiset.sum_empty : multiset.sum (∅ : finset ℕ).val = 0 := by simp

variable [decidable_eq α]
@[simp]
lemma multiset.erase_dup_repeat {a : α} : Π{n : ℕ}, n > 0 → multiset.erase_dup (multiset.repeat a n) = singleton a
| 0 pos := by rcases pos
| 1 pos := by simp
| (n+2) pos := begin
  have : n+1 > 0 := nat.succ_pos n,
  have : multiset.erase_dup (multiset.repeat a (n+1)) = singleton a := multiset.erase_dup_repeat this,
  have : a ∈ multiset.repeat a (n+1) := by simp,
  rw [multiset.repeat_succ, multiset.erase_dup_cons_of_mem this],
  assumption
end
end helpers

namespace finset
/- insert -/
section insert
universe u
variables {α β : Type u} [decidable_eq α] [decidable_eq β]
@[simp]
lemma product_insert {a : α} {s : finset α} {t : finset β} : (insert a s).product t = t.image(λ x, ⟨a, x⟩) ∪ s.product t := begin
  ext ⟨x, y⟩,
  rw [mem_product, mem_union, mem_image, mem_insert],
  split; finish
end
end insert

/- injections -/
section injection
universe u
variables {α β γ : Type u}
def has_domain (f : α → β) (s : finset α) (t : finset β) : Prop := (∀ x ∈ s, f x ∈ t)
def is_injection (f : α → β) (s : finset α) : Prop := ∀ x x' ∈ s, f x = f x' → x = x'
def is_injection_to (f : α → β) (s : finset α) (t : finset β) : Prop := has_domain f s t ∧ is_injection f s

variables {f : α → β} {s s' : finset α} {t : finset β}
lemma disjoint_injection [decidable_eq α] [decidable_eq β] : is_injection f (s ∪ s') → disjoint s s' → disjoint (s.image f) (s'.image f) := begin
  intros inj disj,
  apply disjoint_left.mpr,
  intros y y_in_fs y_in_ft,
  obtain ⟨x_s, ⟨x_s_in_s, eq_s⟩⟩ := mem_image.mp y_in_fs,
  obtain ⟨x_t, ⟨x_t_in_t, eq_t⟩⟩ := mem_image.mp y_in_ft,
  have : x_s = x_t := inj _ _ (mem_union_left _ x_s_in_s) (mem_union_right _ x_t_in_t) (trans eq_s (symm eq_t)),
  exact disjoint_iff_ne.mp disj _ x_s_in_s _ x_t_in_t this,
end

lemma injection_prod_mk {a : α} : is_injection (prod.mk a) s := begin
  intros x x' x_in_s x'_in_s eq,
  simp at eq,
  assumption
end

lemma is_injection_subset : is_injection f s → s' ⊆ s → is_injection f s' := begin
  intros inj subs,
  intros x x' x_in_s x'_in_s fx_is_fx',
  apply inj x x' (subs x_in_s) (subs x'_in_s) fx_is_fx'
end

lemma in_image_injection {a : α} [decidable_eq α] [decidable_eq β] : is_injection f (insert a s) → f a ∈ s.image f → a ∈ s := begin
  intros inj in_image,
  rcases mem_image.mp in_image with ⟨a', a'_in_s, eq⟩,
  suffices : a' = a, {rw [←this], assumption},
  exact inj a' a (mem_insert_of_mem a'_in_s) (mem_insert_self _ _) eq
end

@[simp, to_additive]
lemma prod_image_injection [decidable_eq α] [comm_monoid β] {s : finset γ} {g : γ → α} :
  is_injection g s → (s.image g).prod f = s.prod (λx, f (g x)) := λ inj, prod_image (λx x_in_s y y_in_s, inj x y x_in_s y_in_s)

end injection

/- bijections -/
section bijection
universe u
variables {α β : Type u}
def is_bijection (f : α → β) (s : finset α) (t : finset β) : Prop := (has_domain f s t) ∧ (∀ y ∈ t, ∃! x, x ∈ s ∧ f x = y)

variables {f : α → β} {s : finset α} {t : finset β}
lemma injection_of_bijection : is_bijection f s t → is_injection_to f s t := λ ⟨dom, bij⟩,
  ⟨dom, λ x x' x_in_s x'_in_s fx_is_fx',
  let ⟨x'', ⟨_, unique⟩⟩ := bij (f x) (dom x x_in_s) in
  calc
    x = x'' : unique x ⟨x_in_s, refl _⟩
  ... = x' : symm (unique x' ⟨x'_in_s, symm fx_is_fx'⟩)⟩

@[simp]
lemma product_empty_left {s : finset β} : (∅ : finset α).product s = ∅ := refl _
lemma bijection_empty {u : finset β} : is_bijection f ∅ u -> u = ∅ := begin
  intro bij,
  apply eq_empty_of_forall_not_mem,
  intros y y_in_u,
  obtain ⟨x, ⟨⟨x_in_empty, _⟩, _⟩⟩ := bij.2 y y_in_u,
  exact not_mem_empty x x_in_empty
end

lemma bijection_to_image [decidable_eq β] {s : finset α} {t : finset β} : is_bijection f s t -> s.image f = t := begin
  intro bij,
  ext,
  split; rw [mem_image],
  { rintro ⟨x, x_in_s, fx_is_a⟩,
    rw [←fx_is_a],
    apply bij.1,
    assumption
  },
  intro a_in_t,
  obtain ⟨x, ⟨⟨x_in_s, fx_is_a⟩, _⟩⟩ := bij.2 a a_in_t,
  finish
end
end bijection

/- range -/
@[simp]
lemma geometric_series : Π (n : ℕ), (range n).sum (λ n, 2^n) = 2^n - 1
| 0 := refl _
| (n+1) := calc
  (range (n+1)).sum (λ n, 2^n) = 2^n + (range n).sum (λ n, 2^n) : sum_range_succ _ _
  ... = 2^n + 2^n - 1 : by rw [geometric_series n, ←nat.add_sub_assoc (nat.pow_pos (by norm_num : 2 > 0) n) (2^n)]
  ... = 2^n * 2^1 - 1 : by ring
  ... = 2^(n+1) - 1 : by rw [←nat.pow_add]

/- multiplication -/
def sum_product_is_mul_sum (f : ℕ → ℕ) (s t : finset ℕ) : (s.product t).sum(uncurry (λ a b, f a * f b)) = s.sum f * t.sum f := begin
  rw [sum_product, sum_mul],
  congr,
  ext,
  rw [mul_sum],
  refl
end
end finset
