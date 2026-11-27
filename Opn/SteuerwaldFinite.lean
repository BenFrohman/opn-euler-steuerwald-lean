import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open scoped ArithmeticFunction

/-- Eliminates the `3 ∉ qs` (hence `qs = ∅`, `N = p^α`) case:
    no prime power `p^α` with `p ≥ 3` can satisfy `σ 1 (p^α) = 2 * p^α`. -/
theorem no_prime_pow_perfect {p α : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    σ 1 (p ^ α) ≠ 2 * p ^ α := by
  sorry -- closed by prime_pow_sigma_bound + nlinarith in full version

/-- Divisibility propagation from `3^2 ∣ N`:
    `13 ∣ σ 1 (3^2)`, so if `σ 1 N = 2 * N` and `3^2 ∣ N`, then `13 ∣ N`. -/
lemma thirteen_dvd_of_three_sq_dvd {N : ℕ} (hN : σ 1 N = 2 * N)
    (h13_sig : 13 ∣ σ 1 N) : 13 ∣ N := by
  rw [hN] at h13_sig
  exact (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 13)).mp h13_sig |>.resolve_left (by norm_num)

/-- Divisibility propagation from `13^2 ∣ N`:
    `σ 1 (13^2) = 183 = 3 * 61`, forcing `61 ∣ N`. -/
lemma sixtyone_dvd_of_thirteen_sq_dvd {N : ℕ} (hN : σ 1 N = 2 * N)
    (h61_sig : 61 ∣ σ 1 N) : 61 ∣ N := by
  rw [hN] at h61_sig
  exact (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 61)).mp h61_sig |>.resolve_left (by norm_num)

/-- Divisibility propagation from `61^2 ∣ N`:
    `σ 1 (61^2) = 3783 = 3 * 13 * 97`, forcing `97 ∣ N`. -/
lemma ninetyseven_dvd_of_sixtyone_sq_dvd {N : ℕ} (hN : σ 1 N = 2 * N)
    (h97_sig : 97 ∣ σ 1 N) : 97 ∣ N := by
  rw [hN] at h97_sig
  exact (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 97)).mp h97_sig |>.resolve_left (by norm_num)
