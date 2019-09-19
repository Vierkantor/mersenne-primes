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
    { simp at prod, rw [prod] at copr,
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
    have : coprime (mersenne (k + 1)) (2^(k + 1)) := nat.coprime_sub_one pos_mersenne,
    exact dvd_of_dvd_mul_left (by assumption) (by assumption),
  end,
  rcases mersenne_dvd_l with ⟨m, m_prod⟩,
  rw [m_prod] at *,
  unfold mersenne at *,

  set x := 2^(k + 1) - 1,
  have x_gt_1 : x > 1 := begin
    cases k,
    { linarith },
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
