import data.nat.basic
import tactic.linarith
import tactic.ring

namespace nat
lemma power_geq_1 {k n : ℕ} : (succ k)^n ≥ 1 := begin
induction n,
{ rw [pow_zero], exact le_refl _ },
{ rw [pow_succ], exact _root_.le_add_left n_ih }
end

lemma mul_left_cancel {a b c : ℕ} : a > 0 → a * b = a * c → b = c := λ pos eq, calc
  b = b * a / a : symm (nat.mul_div_cancel _ pos)
  ... = a * b / a : by rw [mul_comm]
  ... = a * c / a : by rw [eq]
  ... = c * a / a : by rw [mul_comm]
  ... = c : nat.mul_div_cancel _ pos

lemma sub_add_from_add_sub : Π {a b c : ℕ}, a ≥ c -> b ≥ c -> a + (b - c) = (a - c) + b
| 0 b c a_ge_c b_ge_c := begin have : c = 0 := by linarith, simp [this] end
| (a+1) 0 c a_ge_c b_ge_c := begin have : c = 0 := by linarith, simp [this] end
| (a+1) (b+1) 0 a_ge_c b_ge_c := by simp
| (a+1) (b+1) (c+1) a_ge_c b_ge_c := begin
  have a_ge_c : a ≥ c := lt_succ_iff.mp a_ge_c,
  have b_ge_c : b ≥ c := lt_succ_iff.mp b_ge_c,
  repeat { rw [add_one] },
  repeat { rw [add_succ] <|> rw [succ_add] },
  repeat { rw [succ_sub_succ] },
  rw [sub_add_from_add_sub a_ge_c b_ge_c]
end
lemma pow_le_pow {a b k : ℕ} : a ≥ b -> a^k ≥ b^k := begin
  intro gt,
  induction k,
  { simp },
  rw [pow_succ, pow_succ],
  exact (mul_le_mul k_ih gt (by linarith) (by linarith))
end
lemma pow_ge_one {a k : ℕ} : a ≥ 1 -> a^k ≥ 1 := λ a_pos, calc
  a^k ≥ 1^k : pow_le_pow a_pos
  ... = 1 : by simp
lemma prime_positive {p : ℕ} : prime p -> p > 0 := λ pr, have h : p ≥ 2 := prime.two_le pr, by linarith
lemma prime_pow_ge_one {p k : ℕ} : prime p -> p^k ≥ 1 :=
  λ pr, pow_ge_one (prime_positive pr)

lemma pow_lt_pow_right {a k l : ℕ} : a > 1 -> k < l -> a^k < a^l := begin
  intros a_big lt,
  induction lt,
  { exact calc
      a^k = 1 * a^k : symm (one_mul _)
      ... < a * a^k : mul_lt_mul a_big (refl _) (pow_ge_one (by linarith)) (by linarith)
      ... = a^k * a : mul_comm _ _
      ... = a^(k + 1) : by simp [pow_succ]},
  exact calc
    a^k = 1 * a^k : symm (one_mul _)
    ... < a * a^lt_b : mul_lt_mul a_big (by linarith) (pow_ge_one (by linarith)) (by linarith)
    ... = a^lt_b * a : mul_comm _ _
    ... = a^(lt_b + 1) : by simp [pow_succ]
end

lemma prod_lt_gt {a a' b b' : ℕ} : b > 0 -> a * b = a' * b' -> a < a' -> b > b' := begin
  intros b_pos eq a_lt_a',
  have : a' * b > a' * b' := calc
  a' * b > a * b : mul_lt_mul_of_pos_right a_lt_a' b_pos
  ... = a' * b' : eq,
  apply lt_of_mul_lt_mul_left this (zero_le _)
end
lemma prod_gt_lt {a a' b b' : ℕ} : a > 0 -> a * b = a' * b' -> b < b' -> a > a' := begin
  rw [mul_comm a b, mul_comm a' b'],
  apply prod_lt_gt
end

lemma pos_of_mul_pos {a b : ℕ} : a * b > 0 -> a > 0 := begin
  cases a,
  { simp },
  intros _,
  exact succ_pos a
end
lemma pos_of_mul_pos_right {a b : ℕ} : a * b > 0 -> b > 0 := begin
  cases b,
  { simp },
  intros _,
  exact succ_pos b
end

lemma pos_of_dvd_pos {a b : ℕ} : b > 0 -> a ∣ b -> a > 0 := begin
  rintros gt ⟨k, prod⟩,
  rw [prod] at gt,
  apply pos_of_mul_pos gt,
end

lemma dvd_pow_succ {p k n : ℕ} : prime p -> n ∣ p^(k + 1) -> n = p^(k + 1) ∨ n ∣ p^k := begin
  rintros pr divides,
  obtain ⟨l , bound, pf⟩ := (dvd_prime_pow pr).1 divides,
  rcases lt_trichotomy l (k+1) with h | h | h,
  { have : l ≤ k := by linarith,
    apply or.inr,
    apply (dvd_prime_pow pr).2,
    finish },
  { apply or.inl,
    rw [pf, h] },
  have : p^(k + 1) > 0 := prime_pow_ge_one pr,
  have : n ≤ p^(k + 1) := le_of_dvd this divides,
  have : p^(k + 1) < p^(k + 1) := calc
  p^(k + 1) < p^l : pow_lt_pow_right (prime.two_le pr) h
  ... = n : symm pf
  ... ≤ p^(k + 1) : this,
  linarith
end

lemma coprime_gcd {a b c : ℕ} : coprime b c → coprime (gcd a b) (gcd a c) :=
  coprime.coprime_dvd_left (gcd_dvd_right a b) ∘
  coprime.coprime_dvd_right (gcd_dvd_right a c)

lemma prod_coprime_gcd {a b c : ℕ} : a > 0 -> coprime b c -> gcd a b * gcd a c = gcd a (b * c) := begin
  intros a_pos coprime,
  apply le_antisymm;
  apply le_of_dvd,
  { exact gcd_pos_of_pos_left _ a_pos },
  { exact nat.coprime.mul_dvd_of_dvd_of_dvd (coprime_gcd coprime) (gcd_dvd_gcd_mul_right_right a b c) (gcd_dvd_gcd_mul_left_right a c b) },
  { exact (mul_lt_mul_left (gcd_pos_of_pos_left _ a_pos)).2 (gcd_pos_of_pos_left _ a_pos) },
  { exact gcd_mul_dvd_mul_gcd _ _ _ }
end
lemma prod_coprime_gcd_left {a b c : ℕ} : c > 0 -> coprime a b -> gcd a c * gcd b c = gcd (a * b) c := begin
  rw [gcd_comm a c, gcd_comm b c, gcd_comm (a * b) c],
  exact prod_coprime_gcd
end

end nat
