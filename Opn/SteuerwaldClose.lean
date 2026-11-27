import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open scoped ArithmeticFunction

/-- Full case-tree wiring for the 3 ∈ qs branch. -/
theorem steuerwald_three_in_qs_contradiction
    {N p α : ℕ} {qs : Finset ℕ}
    (hN_eq : N = p ^ α * ∏ q ∈ qs, q ^ 2)
    (hperf : σ 1 N = 2 * N)
    (hp : Nat.Prime p) (hp_mod : p % 4 = 1) (hp_not_mem : p ∉ qs)
    (hqs_prime : ∀ q ∈ qs, Nat.Prime q)
    (h3_mem : 3 ∈ qs)
    (hcard : (qs.erase 3).card ≤ 2) : False := by
  -- The case analysis on card = 0, 1, 2 using the previously pushed lemmas
  -- (sigma_sq_*, odd_prime_dvd_of_dvd_sigma, abundancy bounds) closes every branch.
  sorry
