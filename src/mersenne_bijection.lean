import algebra.big_operators
import algebra.ordered_ring
import data.int.basic
import data.finset
import data.list
import data.multiset
import data.nat.basic
import data.nat.gcd
import data.nat.prime
import logic.basic
import logic.function
import tactic.find
import tactic.linarith
import tactic.norm_num
import tactic.ring

import divisor
import finset
import nat

open finset (range)
open function (uncurry)
open nat (coprime prime)
open nat.coprime
open nat.divisor
open tactic.interactive («apply» cases contradiction «have» «intro» «intros» «suffices»)
open interactive (parse)
open interactive.types (texpr)
open lean.parser (ident many tk)

section tactics
open tactic.interactive («apply» cases contradiction «have» «intro» «intros» «suffices»)
open interactive (parse)
open interactive.types (texpr)
open lean.parser (ident many tk)

/--
Tactic for showing equalities in a quotient: show they hold for all representatives.
--/
meta def tactic.interactive.representative : parse (many ident) -> tactic unit := λ as, do
  «intros» as,
  as.mmap (λ a, do
  local_a <- tactic.get_local a,
  «apply» ``(quotient.induction_on %%local_a)),
  «intros» as,
  «apply» ``(quotient.sound)

meta def tactic.interactive.decide : parse (prod.mk <$> ident <* tk ":" <*> texpr) -> tactic unit
  | ⟨h , p⟩ := do
  «have» (some h) (some ``(%%p ∨ ¬ %%p)) ``(dec_em %%p),
  local_h <- tactic.get_local h,
  cases (none, ``(%%local_h)) [h]

meta def tactic.interactive.absurd : tactic unit := do
  «suffices» none (some ``(false)),
  contradiction
end tactics

def mersenne : ℕ -> ℕ := λ n, 2^n - 1
@[simp]
lemma mersenne_def {n : ℕ} : mersenne n = 2^n - 1 := refl _

def nat_multiplicative (f : ℕ → ℕ) : Prop := ∀ a b ≥ 1, coprime a b -> f (a * b) = f a * f b

@[simp]
lemma divisor_sum_multiplicative : nat_multiplicative σ := begin
  intros a b a_pos b_pos coprime,
  suffices : finset.is_bijection (uncurry ((*) : ℕ → ℕ → ℕ)) (finset.product (divisors a) (divisors b)) (divisors (a * b)),
  { unfold σ,
    exact calc
      finset.sum (divisors (a * b)) id = finset.sum ((finset.product (divisors a) (divisors b)).image (uncurry (*))) id : by rw [finset.bijection_to_image this]
      ... = finset.sum (finset.product (divisors a) (divisors b)) (uncurry (*)) : finset.sum_image_injection (finset.injection_of_bijection this).2
      ... = finset.sum (finset.product (divisors a) (divisors b)) (uncurry (λ a b, id a * id b)) : by congr
      ... = finset.sum (divisors a) id * finset.sum (divisors b) id : finset.sum_product_is_mul_sum id (divisors a) (divisors b)
  },

  have : a * b > 0 := calc
    a * b > 0 * b : (@mul_lt_mul_right _ _ 0 a b b_pos).2 a_pos
    ... = 0 : by norm_num,

  split,
  { rintros ⟨d, d'⟩ dd'_in_prod,
    rcases (finset.mem_product.1 dd'_in_prod) with ⟨d_div_a, d'_div_b⟩,
    rw [←divisor_iff_dvd] at *,
    have dd'_div_ab := mul_dvd_mul d_div_a d'_div_b,
    repeat {finish} },

  intros y div,
  use ⟨nat.gcd y a, nat.gcd y b⟩,

  replace div := (divisor_iff_dvd (by assumption)).2 div,
  have : nat.gcd y a ∈ divisors a := (divisor_iff_dvd (by assumption)).mp (nat.gcd_dvd_right y a),
  have : nat.gcd y b ∈ divisors b := (divisor_iff_dvd (by assumption)).mp (nat.gcd_dvd_right y b),
  have := nat.prod_coprime_gcd (nat.pos_of_dvd_pos (by assumption) div) coprime,
  split,
  { split, { finish }, exact calc
      nat.gcd y a * nat.gcd y b = nat.gcd y (a * b) : this
      ... = y : nat.gcd_eq_left div
      },
  rintros ⟨y1, y2⟩ ⟨in_div, prod⟩,
  rcases finset.mem_product.mp in_div with ⟨y1_div_a, y2_div_b⟩,
  replace y1_div_a := (divisor_iff_dvd (by assumption)).2 y1_div_a,
  replace y2_div_b := (divisor_iff_dvd (by assumption)).2 y2_div_b,
  simp at prod,
  rw [←prod] at *,

  have y1_coprime_b : nat.coprime y1 b := coprime_dvd_left y1_div_a coprime,
  have y2_coprime_a : nat.coprime y2 a := (coprime_dvd_right y2_div_b coprime).symm,
  have : nat.gcd (y1 * y2) a = y1 := calc
    nat.gcd (y1 * y2) a = nat.gcd y1 a : nat.coprime.gcd_mul_right_cancel y1 y2_coprime_a
    ... = y1 : nat.gcd_eq_left y1_div_a,
  have : nat.gcd (y1 * y2) b = y2 := calc
    nat.gcd (y1 * y2) b = nat.gcd y2 b : nat.coprime.gcd_mul_left_cancel y2 y1_coprime_b
    ... = y2 : nat.gcd_eq_left y2_div_b,
  finish
end

theorem perfect_from_mersenne (n : ℕ) : prime (mersenne (n+1)) -> perfect (2^n * mersenne (n+1)) := begin
  intro pr,
  have : mersenne (n + 1) ≥ 2 := nat.prime.two_le pr,
  have : coprime (2^n) (mersenne (n+1)),
  { apply nat.coprime.pow_left,
    apply (nat.coprime_primes _ _).2,
    { cases n,
      { unfold mersenne, simp, linarith },
      unfold mersenne,
      rw [nat.pow_succ, nat.pow_succ],
      suffices : 2^n * 4 > 3,
      { apply ne_of_lt,
        exact calc 2 = 3 - 1 : by simp
          ... < 2^n * 4 - 1 : nat.lt_pred_iff.2 this
          ... = 2^n * (2 * 2) - 1 : refl _
          ... = 2^n * 2 * 2 - 1 : by rw [mul_assoc]
        },
      have : 2^n ≥ 1 := nat.power_geq_1,
      linarith
    },
    { exact nat.prime_two },
    assumption },
  apply eq.trans (divisor_sum_multiplicative _ _ (nat.power_geq_1) (by linarith) this),
  rw [divisor_sum_prime_power nat.prime_two, divisor_sum_prime pr, finset.geometric_series],
  rw [mul_add, mul_one, nat.mul_sub_right_distrib, one_mul],
  rw [←mersenne_def, nat.pow_succ],
  set x := mersenne (n + 1),
  have : 2^n * 2 * x ≥ x := calc
    2^n * 2 * x = 2^n * (2 * x) : nat.mul_assoc _ _ _
    ... ≥ 1 * (1 * x) : mul_le_mul (nat.power_geq_1) (mul_le_mul (by linarith) (refl x) (by linarith) (by linarith)) (by linarith) (by linarith)
    ... = x : by simp,
  rw [nat.sub_add_from_add_sub (refl x) this, nat.sub_self, nat.zero_add],
  ring
end

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

open nat (succ)

@[simp]
lemma gcd_add {a b : ℕ} : nat.gcd a (a + b) = nat.gcd b a := begin
  cases a,
  { simp },
  cases b,
  { simp },
  exact calc
    nat.gcd (succ a) (succ a + succ b)
        = nat.gcd (succ b % succ a) (succ a) : by rw [nat.gcd_succ, nat.add_mod_left]
    ... = nat.gcd (succ b) (succ a) : by rw [←nat.gcd_succ, nat.gcd_comm]
end

theorem coprime_sub_one {n : ℕ} : n > 0 -> coprime (n - 1) n := begin
  intro n_pos,
  cases n,
  { absurd, linarith },
  exact calc
    nat.gcd ((n + 1) - 1) (n + 1) = nat.gcd 1 n : by simp
    ... = 1 : nat.gcd_one_left _
end

theorem mersenne_from_perfect (n : ℕ) : n > 0 -> perfect (2 * n) -> ∃ k, 2 * n = 2^k * mersenne (k + 1) ∧ prime (mersenne (k+1)) := begin
  intros n_pos perfect,
  have pos_2n : 2 * n > 0 := calc
    2 * n > 2 * 0 : (mul_lt_mul_left (by norm_num)).2 n_pos
    ... = 0 : by norm_num,
  rcases divide_out_factors 2 nat.prime_two (2 * n) pos_2n with ⟨k, l, prod, copr⟩,
  use k,

  rw [←prod] at *,
  have k_pos : k > 0 := begin
    cases k,
    { absurd, simp at prod, rw [prod] at copr,
      have : 2 = 1 := calc
        2 = nat.gcd 2 (2 * n) : symm (nat.gcd_mul_right_right n 2)
        ... = 1 : copr,
      norm_num at this },
    exact nat.succ_pos k
  end,

  have l_pos : l > 0 := begin cases l, { cases copr }, exact nat.succ_pos _ end,
  have pos_2k : 2^k > 0 := nat.pow_pos (by norm_num) k,
  have pos_mersenne : 2^(k + 1) > 0 := nat.pow_pos (by norm_num) (k+1),
  have coprime_2k_l : coprime (2^k) l := pow_left k copr,

  unfold nat.divisor.perfect at perfect,
  rw [divisor_sum_multiplicative (2 ^ k) l pos_2k l_pos coprime_2k_l, divisor_sum_prime_power nat.prime_two, finset.geometric_series] at perfect,
  have mersenne_dvd_l : mersenne (k + 1) ∣ l := begin
    have : mersenne (k + 1) ∣ 2^(k+1) * l := ⟨σ l, by rw [mersenne, perfect, nat.pow_succ, nat.mul_comm (2^k) 2, nat.mul_assoc]⟩,
    have : coprime (mersenne (k + 1)) (2^(k + 1)) := coprime_sub_one pos_mersenne,
    exact dvd_of_dvd_mul_left (by assumption) (by assumption),
  end,
  rcases mersenne_dvd_l with ⟨m, m_prod⟩,
  rw [m_prod] at *,
  unfold mersenne at *,

  set x := 2^(k + 1) - 1,
  have x_gt_1 : x > 1 := begin
    cases k,
    { absurd, linarith },
    have : 2^k * 2 * 2 ≥ 1 + (2 * 2 - 1) := calc
      2^k * 2 * 2 = 2^k * 4 : nat.mul_assoc (2^k) 2 2
      ... ≥ 1 * 4 : @mul_le_mul _ _ 1 4 (2^k) 4 (nat.pow_pos (by norm_num) k) (refl _) (by norm_num) (by norm_num)
      ... = 4 : nat.one_mul _
      ... = 1 + (2 * 2 - 1) : by norm_num,
    exact calc
      x = 2^(k + 2) - 1 : refl _
      ... = 2^k * 2 * 2 - 1 : by rw [nat.pow_succ, nat.pow_succ]
      ... ≥ 1 * 2 * 2 - 1 : nat.le_sub_left_of_add_le this
      ... > 1 : by norm_num
  end,
  have x_pos : x > 0 := by linarith,

  replace perfect := congr_arg (λ n, n / x) perfect,
  simp at perfect,
  have : x ∣ 2^k * x * m := begin
    use 2^k * m,
    rw [←mul_assoc, mul_comm (2^k) x]
  end,
  have : 2^k * x * m / x = 2^k * m := by rw [mul_assoc, mul_comm x m, ←mul_assoc, nat.mul_div_cancel _ x_pos],
  rw [mul_comm x (σ (x * m)), ←mul_assoc (2^k) x m, nat.mul_div_assoc 2 (by assumption), nat.mul_div_cancel _ x_pos, this] at perfect,
  have sigma_l : σ (x * m) = x * m + m := calc
    σ (x * m) = 2 * (2^k * m) : perfect
    ... = 2 * 2^k * m : symm (mul_assoc 2 (2^k) m)
    ... = 2^(k + 1) * m : by rw [mul_comm 2 (2^k), ←nat.pow_succ 2 k]
    ... = (2^(k + 1) - 1 + 1) * m : by rw [@nat.sub_add_cancel (2^(k + 1)) 1 pos_mersenne]
    ... = (x + 1) * m : refl _
    ... = x * m + 1 * m : add_mul (2^(k+1) - 1) 1 m
    ... = x * m + m : by rw [one_mul],
  have m_pos : m > 0 := (mul_lt_mul_left x_pos).mp l_pos,

  have m_is_one : m = 1 := divisor_sum_is_sum x_gt_1 m_pos sigma_l,
  simp [m_is_one] at *,
  exact prime_from_divisor_sum x_gt_1 sigma_l
end
