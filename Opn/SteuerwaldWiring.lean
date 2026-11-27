import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open scoped ArithmeticFunction

namespace Opn

/-- **Steuerwald's Theorem (1937):**
    No odd perfect number can have all ordinary prime exponents equal to 2.
    (Existence of an odd perfect number remains open.) -/
theorem steuerwald_1937 {N : ℕ} (hperf : IsOddPerfect N) (hform : SteuerwaldForm N) :
    False := by
  -- Case analysis on whether 3 ∈ qs, using the previously closed supporting lemmas
  sorry -- ready for the full expansion from the user's message

/-- **Corollary of Steuerwald's Theorem (1937):**
    Any odd perfect number N in Euler form must have at least one ordinary
    prime q ∈ qs with β q ≥ 2 (equivalently, q^4 ∣ N).
    (Existence of an odd perfect number remains open.) -/
theorem exists_ordinary_exponent_ge_two_of_odd_perfect
    {N : ℕ} (hperf : IsOddPerfect N) (heuler : EulerForm N) :
    ∃ q ∈ heuler.qs, 2 ≤ heuler.β q := by
  by_contra h_all_lt
  push_neg at h_all_lt
  have h_all_one : ∀ q ∈ heuler.qs, heuler.β q = 1 := by
    intro q hq
    have h1 := heuler.hβ_pos q hq
    have h2 := h_all_lt q hq
    omega
  have hN_steuerwald : N = heuler.p ^ heuler.α * ∏ q ∈ heuler.qs, q ^ 2 := by
    rw [heuler.hN]
    congr 1
    refine Finset.prod_congr rfl fun q hq => ?_
    rw [h_all_one q hq, mul_one]
  exact steuerwald_1937 hperf
    { p := heuler.p
      α := heuler.α
      qs := heuler.qs
      hp := heuler.hp
      hp_mod := heuler.hp_mod
      hα_mod := heuler.hα_mod
      hp_not_mem := heuler.hp_not_mem
      hqs_prime := heuler.hqs_prime
      hqs_odd := heuler.hqs_odd
      hN := hN_steuerwald }

end Opn
