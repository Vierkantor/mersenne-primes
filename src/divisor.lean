import algebra.big_operators
import data.finset
import data.nat.basic

import nat

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

end nat.divisor
