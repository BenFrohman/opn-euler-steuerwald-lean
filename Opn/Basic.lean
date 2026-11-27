import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.NumberTheory.Padics.PadicVal

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

/-- Cyclotomic divisibility: primes dividing Φ_r(q) are r or ≡ 1 mod r. -/
theorem prime_dvd_cyclotomic {r q ℓ : ℕ} (hr : Nat.Prime r) (hq : Nat.Prime q)
    (hℓ : Nat.Prime ℓ) (h : ℓ ∣ eval q (cyclotomic r ℤ)) :
    ℓ = r ∨ ℓ % r = 1 := by
  -- Standard ZMod order argument
  by_cases hℓr : ℓ = r
  · left; exact hℓr
  · right
    -- order of q mod ℓ divides r but not any proper divisor
    have hord : orderOf (q : ZMod ℓ) = r := by
      sorry -- complete with Mathlib cyclotomic evaluation lemmas
    exact orderOf_dvd_iff_pow_eq_one.mp (by simp [hord])

/-- Steuerwald 1937: no OPN with all ordinary exponents exactly 2. -/
theorem steuerwald {n : ℕ} (hn : IsOddPerfect n) (ef : EulerForm n)
    (heq : ∀ q ∈ ef.m.primeFactors, n.factorization q = 2) :
    False := by
  -- 3 divides n
  have h3 : 3 ∣ n := by
    sorry -- from cyclotomic residue
  by_cases hps : ef.p = 3
  · -- valuation mismatch via chain
    have : padicValNat 3 (σ 1 n) > ef.α := by
      sorry -- explicit chain 3,13,61,...
    have : padicValNat 3 (2 * n) = ef.α := by
      simp [hn.2.2, hps]
    linarith
  · -- ordinary 3 forces higher exponent
    sorry
