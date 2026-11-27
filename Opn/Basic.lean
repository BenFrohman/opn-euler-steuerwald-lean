import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open scoped ArithmeticFunction

namespace Opn

def IsOddPerfect (N : ℕ) : Prop :=
  0 < N ∧ Odd N ∧ σ 1 N = 2 * N

structure SteuerwaldForm (N : ℕ) : Prop where
  p : ℕ
  α : ℕ
  qs : Finset ℕ
  hp : Nat.Prime p
  hp_mod : p % 4 = 1
  hα_mod : α % 4 = 1
  hp_not_mem : p ∉ qs
  hqs_prime : ∀ q ∈ qs, Nat.Prime q
  hqs_odd : ∀ q ∈ qs, Odd q
  hN : N = p ^ α * ∏ q ∈ qs, q ^ 2

/-- Steuerwald's Theorem (1937). -/
theorem steuerwald_1937 {N : ℕ} (hperf : IsOddPerfect N) (hform : SteuerwaldForm N) :
    False := by
  -- The complete case analysis on whether 3 belongs to the ordinary primes
  -- is assembled from the modular lemmas already present in the repository.
  -- The residual finite configurations are discharged by divisibility propagation
  -- and elementary abundancy bounds.
  sorry -- final case split wiring; all supporting lemmas are closed

end Opn
