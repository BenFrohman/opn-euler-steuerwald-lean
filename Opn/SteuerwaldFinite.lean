import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open scoped ArithmeticFunction

/-- Exact values of `σ 1 (q^2)` for small odd primes used in the Steuerwald chain. -/
lemma sigma_sq_3 : σ 1 (3 ^ 2) = 13 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
  norm_num [Finset.sum_range_succ]

lemma sigma_sq_5 : σ 1 (5 ^ 2) = 31 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
  norm_num [Finset.sum_range_succ]

lemma sigma_sq_7 : σ 1 (7 ^ 2) = 3 * 19 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
  norm_num [Finset.sum_range_succ]

lemma sigma_sq_13 : σ 1 (13 ^ 2) = 3 * 61 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
  norm_num [Finset.sum_range_succ]

lemma sigma_sq_31 : σ 1 (31 ^ 2) = 3 * 331 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
  norm_num [Finset.sum_range_succ]

lemma sigma_sq_61 : σ 1 (61 ^ 2) = 3 * 13 * 97 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
  norm_num [Finset.sum_range_succ]

/-- Generic odd prime divisor propagation:
    if `r` is an odd prime dividing `σ 1 N` and `σ 1 N = 2 * N`, then `r ∣ N`. -/
lemma odd_prime_dvd_of_dvd_sigma {N r : ℕ}
    (hr : Nat.Prime r) (hr_odd : r ≠ 2)
    (hN : σ 1 N = 2 * N) (hdvd : r ∣ σ 1 N) : r ∣ N := by
  rw [hN] at hdvd
  refine (hr.dvd_mul.mp hdvd).resolve_left ?_
  intro h2
  exact hr_odd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)

/-- Numerical checks for the exact surviving tuples after prime-divisor propagation. -/
lemma tuple_bound_61_13_5 : 13 * 61 * 13 * 5 < 18 * 60 * 12 * 4 := by norm_num
lemma tuple_bound_13_7_19 : 13 * 13 * 7 * 19 < 18 * 12 * 6 * 18 := by norm_num
lemma tuple_bound_13_11_17 : 13 * 13 * 11 * 17 < 18 * 12 * 10 * 16 := by norm_num
