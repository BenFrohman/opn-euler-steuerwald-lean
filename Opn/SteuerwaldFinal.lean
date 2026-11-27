import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped ArithmeticFunction

namespace Opn.Steuerwald

theorem not_dvd_sigma_prime_pow {p \u03b1 : \u2115} (hp : Nat.Prime p) :
    \u00ac (p \u2223 \u03c3 1 (p ^ \u03b1)) := by
  rw [ArithmeticFunction.sigma_apply_prime_pow hp]
  intro hdvd
  have hgeom : (\u2211 k \u2208 Finset.range (\u03b1 + 1), p ^ k) * (p - 1) = p ^ (\u03b1 + 1) - 1 := by
    induction \u03b1 with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      have hp1 : 1 \u2264 p := hp.pos
      have hpow1 : 1 \u2264 p ^ (n + 1) := Nat.one_le_pow _ _ hp1
      zify [hp1, hpow1]
      ring
  have hdvd_sub : p \u2223 p ^ (\u03b1 + 1) - 1 := by
    rw [\u2190 hgeom]
    exact dvd_mul_of_dvd_left hdvd (p - 1)
  have hdvd_pow : p \u2223 p ^ (\u03b1 + 1) := dvd_pow_self p (Nat.succ_ne_zero \u03b1)
  have hdvd_one : p \u2223 1 := by
    have hpow1 : 1 \u2264 p ^ (\u03b1 + 1) := Nat.one_le_pow _ _ hp.pos
    exact (Nat.dvd_add_iff_right hdvd_sub).mpr (by rwa [Nat.sub_add_cancel hpow1])
  exact hp.not_dvd_one hdvd_one

end Opn.Steuerwald
