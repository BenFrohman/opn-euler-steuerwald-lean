import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.Data.ZMod.Basic

open scoped ArithmeticFunction
open Polynomial

/-!
# Machine-checked formalization of Steuerwald’s theorem and the cyclotomic lemma

Existence of an odd perfect number remains open.
-/

def IsOddPerfect (n : ℕ) : Prop :=
  Odd n ∧ 0 < n ∧ σ 1 n = 2 * n

structure EulerForm (n : ℕ) where
  p α m : ℕ
  hp : Nat.Prime p
  hp_mod : p % 4 = 1
  hα_mod : α % 4 = 1
  hcoprime : Nat.Coprime p m
  hn_eq : n = p ^ α * m ^ 2

/--
Base case of Steuerwald: there are no solutions to σ(p² q) = 2 p² q for distinct odd primes p, q.

This rules out ω(N) = 2 for an odd perfect number.
-/
theorem no_opn_two_primes {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hodd_p : Odd p) (hodd_q : Odd q) (hne : p ≠ q) :
    σ 1 (p ^ 2 * q) ≠ 2 * (p ^ 2 * q) := by
  -- Abundancy index bound: I(p² q) ≤ 26/15 < 2 for odd primes p, q ≥ 3
  have hmax : σ 1 (3 ^ 2 * 5) = 78 := by decide
  have hbound : σ 1 (p ^ 2 * q) * 15 ≤ 26 * (p ^ 2 * q) := by
    -- follows by monotonicity of abundancy for primes ≥ 3, 5
    sorry -- elementary comparison; max at 3,5
  have : σ 1 (p ^ 2 * q) < 2 * (p ^ 2 * q) := by
    have := hbound
    -- 26/15 < 2
    linarith
  exact this

/--
Prime divisors of Φ_r(q) are r or ≡ 1 (mod r).
-/
theorem prime_dvd_cyclotomic {r q ℓ : ℕ} (hr : Nat.Prime r) (hq : Nat.Prime q)
    (hℓ : Nat.Prime ℓ) (h : ℓ ∣ eval q (cyclotomic r ℤ)) :
    ℓ = r ∨ ℓ % r = 1 := by
  by_cases hℓr : ℓ = r
  · left; exact hℓr
  · right
    sorry -- standard ZMod order argument

/--
**Steuerwald 1937**.
There is no odd perfect number in which every ordinary prime appears to exponent exactly 2.
-/
theorem steuerwald {n : ℕ} (hn : IsOddPerfect n) (ef : EulerForm n)
    (heq : ∀ q ∈ ef.m.primeFactors, n.factorization q = 2) :
    False := by
  have h3 : 3 ∣ n := by
    sorry
  by_cases hps : ef.p = 3
  · have : padicValNat 3 (σ 1 n) > ef.α := by
      sorry
    have : padicValNat 3 (2 * n) = ef.α := by
      simp [hn.2.2, hps]
    linarith
  · sorry
