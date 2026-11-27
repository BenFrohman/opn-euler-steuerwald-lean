import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped ArithmeticFunction BigOperators

namespace Opn.Steuerwald

theorem sigma_prod_prime_sq {\u03b9 : Type*} [DecidableEq \u03b9] (s : Finset \u03b9) (q : \u03b9 \u2192 \u2115)
    (hq_prime : \u2200 i \u2208 s, Nat.Prime (q i))
    (hq_inj : Set.InjOn q s) :
    \u03c3 1 (\u220f i \u2208 s, q i ^ 2) = \u220f i \u2208 s, (q i ^ 2 + q i + 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have ha_prime : Nat.Prime (q a) := hq_prime a (Finset.mem_insert_self a s)
    have hs_prime : \u2200 i \u2208 s, Nat.Prime (q i) :=
      fun i hi => hq_prime i (Finset.mem_insert_of_mem hi)
    have hcop : Nat.Coprime (q a ^ 2) (\u220f i \u2208 s, q i ^ 2) := by
      refine Nat.Coprime.prod_right fun i hi => ?_
      have hne : q a \u2260 q i := fun heq =>
        ha (hq_inj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) heq \u25b8 hi)
      exact ((ha_prime.coprime_iff_not_dvd.mpr fun h =>
        hne ((Nat.prime_dvd_prime_iff_eq ha_prime (hs_prime i hi)).mp h)).pow_left 2).pow_right 2
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ih hs_prime (hq_inj.mono (Finset.subset_insert a s)),
        ArithmeticFunction.sigma_apply_prime_pow ha_prime]
    norm_num [Finset.sum_range_succ]
    ring

end Opn.Steuerwald
