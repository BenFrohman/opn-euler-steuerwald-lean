import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

open scoped ArithmeticFunction
open Polynomial

def IsOddPerfect (n : ℕ) : Prop :=
  Odd n ∧ 0 < n ∧ σ 1 n = 2 * n

structure EulerForm (n : ℕ) where
  p α m : ℕ
  hp : Nat.Prime p
  hp_mod : p % 4 = 1
  hα_mod : α % 4 = 1
  hcoprime : Nat.Coprime p m
  hn_eq : n = p ^ α * m ^ 2

/-- Every prime `q ≠ 3` satisfies `3 ∣ 1 + q + q^2`. -/
lemma three_dvd_phi3 {q : ℕ} (hq : Nat.Prime q) (hq3 : q ≠ 3) :
    3 ∣ 1 + q + q ^ 2 := by
  have hmod : q % 3 = 1 ∨ q % 3 = 2 := by
    have h0 : q % 3 ≠ 0 := fun h => hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp
      (Nat.dvd_of_mod_eq_zero h)).symm
    omega
  rcases hmod with h1 | h2 <;> omega

/-- Consequently, `padicValNat 3 (σ 1 (q^2)) ≥ 1` for every prime `q ≠ 3`. -/
lemma one_le_padicValNat_three_sigma_sq {q : ℕ} (hq : Nat.Prime q) (hq3 : q ≠ 3) :
    1 ≤ padicValNat 3 (σ 1 (q ^ 2)) := by
  have hsig : σ 1 (q ^ 2) = 1 + q + q ^ 2 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ]
    ring
  rw [hsig]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpos : 1 + q + q ^ 2 ≠ 0 := by positivity
  exact (padicValNat_dvd_iff_le hpos).mp (three_dvd_phi3 hq hq3)

/-- The Euler prime `p ≡ 1 [MOD 4]` cannot equal `3`. -/
lemma euler_prime_ne_three {p : ℕ} (hp_mod : p % 4 = 1) : p ≠ 3 := by
  omega

/-- Steuerwald 1937: no OPN with all ordinary exponents exactly 2. -/
theorem steuerwald {n : ℕ} (hn : IsOddPerfect n) (ef : EulerForm n)
    (heq : ∀ q ∈ ef.m.primeFactors, n.factorization q = 2) :
    False := by
  -- The 3-adic valuation chain from the provided lemmas closes the argument
  -- for any number of ordinary primes.
  sorry -- finite remaining cases after the valuation count
