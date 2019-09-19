import algebra.big_operators
import data.finset
import data.nat.basic

import nat

section tactics
open tactic.interactive («apply» cases contradiction «have» «intro» «intros» «suffices»)
open interactive (parse)
open interactive.types (texpr)
open lean.parser (ident many tk)

meta def tactic.interactive.decide : parse (prod.mk <$> ident <* tk ":" <*> texpr) -> tactic unit
| ⟨h , p⟩ := do
  «have» (some h) (some ``(%%p ∨ ¬ %%p)) ``(dec_em %%p),
  local_h <- tactic.get_local h,
  cases (none, ``(%%local_h)) [h]
end tactics


namespace nat.divisor
open nat

open finset (range)
def divisors : ℕ -> finset ℕ := λ n, (range (n+1)).filter (λ d, d ∣ n)
def σ : ℕ -> ℕ := λ n, (divisors n).sum id
def perfect : ℕ -> Prop := λ n, σ n = 2 * n

def divisor_iff_dvd {d n : ℕ} : n > 0 → (d ∣ n ↔ d ∈ divisors n) := begin
  intro n_pos,
  split;
  intro h,
  { rw [divisors, finset.mem_filter, finset.mem_range],
    have : d < n + 1 := lt_succ_iff.mpr (nat.le_of_dvd n_pos h),
    finish
    },
  { unfold divisors at h,
    rw [finset.mem_filter] at h,
    finish }
end

lemma divisors_pow_succ {p k : ℕ} : prime p -> divisors (p^(k + 1)) = insert (p^(k + 1)) (divisors (p^k)) := begin
  intro pr,
  have : p^k > 0 := nat.prime_pow_ge_one pr,
  unfold divisors,
  rw [finset.range_succ, finset.filter_insert],
  simp,
  congr' 1,
  ext,
  rw [finset.mem_filter, finset.mem_filter],
  rw [finset.mem_range, finset.mem_range],
  constructor;
  rintros ⟨bound, divides⟩,
  { cases dvd_pow_succ pr divides,
    { by_contra, exact ne_of_lt bound h },
    have : a < 1 + p^k := calc
      a ≤ p^k : nat.le_of_dvd this h
      ... < nat.succ (p^k) : lt_add_one (p^k)
      ... = 1 + p^k : symm (nat.one_add _),
    finish },
  split,
  { exact calc
  a ≤ p^k : nat.le_of_dvd this divides
  ... = 1 * p^k : symm (nat.one_mul _)
  ... < p * p^k : mul_lt_mul (nat.prime.two_le pr) (refl _) (by assumption) (by linarith)
  ... = p^(k + 1) : by simp [mul_comm, nat.pow_succ] },
  exact dvd_mul_of_dvd_left divides p
end

lemma divisor_sum_prime_power {p k : ℕ} : prime p -> σ (p ^ k) = (range (k+1)).sum (λ n, p^n) := begin
  intro pr,
  induction k,
  { simp, refl },
  suffices : σ (p^(k_n+1)) = σ (p^k_n) + p^(k_n+1),
  { simp [this, k_ih, finset.sum_range_succ] },
  have : p^(k_n + 1) ∉ divisors (p^k_n),
  { unfold divisors,
    rw [finset.mem_filter],
    rintro ⟨in_range, divides⟩,
    have : p^k_n > p^k_n := calc
    p^k_n ≥ p^(k_n + 1) : nat.le_of_dvd (nat.prime_pow_ge_one pr) divides
    ... = p * p^k_n: by rw [nat.pow_succ, mul_comm]
    ... > 1 * p^k_n : mul_lt_mul (nat.prime.two_le pr) (refl _) (nat.prime_pow_ge_one pr) (by linarith)
    ... = p^k_n : one_mul _,
    linarith },
  unfold σ,
  simp [divisors_pow_succ pr, finset.sum_insert this]
end

lemma divisor_sum_prime {p : ℕ} : prime p -> σ p = 1 + p := λ pr, calc
  σ p = σ (p ^ 1) : by simp
  ... = (range (1+1)).sum (λ n, p^n) : divisor_sum_prime_power pr
  ... = 1 + p^1 : refl _
  ... = 1 + p : by simp

lemma mul_gt_one {a b : ℕ} : a > 1 -> b > 0 -> a * b > b := λ a_gt_one b_pos,
  calc b = 1 * b : symm (one_mul _)
  ... < a * b : nat.mul_lt_mul_of_pos_right a_gt_one b_pos

lemma divide_out_factors (p : ℕ) (pr : prime p) : Π (n : ℕ), n > 0 → ∃ k l : ℕ, p^k * l = n ∧ nat.coprime p l
| n n_pos := begin
  decide h : p ∣ n,
  { have p_pos : p > 0 := (have this : p ≥ 2 := nat.prime.two_le pr, by linarith),
    have : n ≥ p := nat.le_of_dvd n_pos h,
    have next_pos : n / p > 0 := nat.div_pos this p_pos,
    let recursion_helper : n / p < n := nat.div_lt_of_lt_mul (mul_gt_one (nat.prime.two_le pr) n_pos),
    rcases divide_out_factors (n / p) next_pos with ⟨k, l, prod, copr⟩,
    use (nat.succ k),
    use l,
    split,
    { rw [nat.pow_succ, mul_comm (p^k) p, mul_assoc, prod, ←nat.mul_div_assoc _ h, nat.mul_div_cancel_left _ p_pos] },
    assumption },
  use 0,
  use n,
  simp,
  exact (nat.prime.coprime_iff_not_dvd pr).mpr h,
end using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.fst⟩]}

lemma divisor_sum_ge {n : ℕ} (ds : list ℕ) : n > 0 -> (∀ d ∈ ds, d ∣ n) -> multiset.nodup ds -> σ n ≥ ds.sum := begin
  unfold σ,
  intros n_pos divs nd,
  let ds' : finset ℕ := ⟨ds, nd⟩,
  have : ds' ⊆ (divisors n) := finset.subset_iff.mpr (λ d d_in, (divisor_iff_dvd n_pos).mp (divs d d_in)),
  exact calc
    finset.sum (divisors n) id ≥ finset.sum ds' id : finset.sum_le_sum_of_subset this
    ... = (ds.map id).sum : multiset.coe_sum _
    ... = ds.sum : by rw [list.map_id]
end

lemma divisor_sum_is_sum {a b : ℕ} : a > 1 -> b > 0 -> σ (a * b) = a * b + b -> b = 1 := begin
  intros a_gt_1 b_pos eq,
  have ab_pos := calc 1 ≤ b : b_pos ... < a * b : mul_gt_one a_gt_1 b_pos,
  by_contra,
  suffices : σ (a * b) ≥ a * b + b + 1,
  { linarith },
  have divs : ∀ d ∈ [a * b, b, 1], d ∣ a * b := by { rintros d (h | h | h | h); rcases h; norm_num },
  suffices : multiset.nodup [a * b, b, 1],
  { exact calc
      σ (a * b) ≥ [a * b, b, 1].sum : divisor_sum_ge _ (by linarith) divs this
      ... = a * b + b + 1 : by simp },
  have : a * b ≠ b := ne_of_gt (mul_gt_one a_gt_1 b_pos),
  have : a * b ≠ 1 := ne_of_gt (by assumption),
  finish
end

lemma prime_from_divisor_sum {p : ℕ} : p > 1 → σ (p) = p + 1 -> prime p := begin
  intros p_gt_1 eq,
  by_contra np,
  rcases nat.exists_dvd_of_not_prime p_gt_1 np with ⟨d, d_div_p, d_ne_one, d_ne_p⟩,
  have : d > 0 := begin
    suffices : d ≠ 0, { cases d, contradiction, exact nat.succ_pos _ },
    rcases d_div_p with ⟨k, prod⟩, rintro rfl, apply d_ne_p, simp [prod]
  end,
  suffices : σ p ≥ p + d + 1, { linarith },
  have : multiset.nodup [p, d, 1],
  { have : p ≠ 1 := ne_of_gt p_gt_1,
    finish
  },
  have divs : ∀ d' ∈ [p, d, 1], d' ∣ p := by { rintros d' (h | h | h | h); rcases h; repeat {norm_num}, assumption },
  exact calc
    σ p ≥ [p, d, 1].sum : divisor_sum_ge _ (by linarith) divs this
    ... = p + d + 1 : by simp
end

end nat.divisor
