import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped ArithmeticFunction

namespace Opn.Steuerwald

/-- Cyclotomic divisibility for Φ₃(q). -/
theorem prime_dvd_phi3 {q r : ℕ} (hr : Nat.Prime r) (hdvd : r ∣ q ^ 2 + q + 1) :
    r = 3 ∨ r ≡ 1 [MOD 3] := by
  by_cases hr3 : r = 3
  · exact Or.inl hr3
  · right
    haveI : Fact (Nat.Prime r) := ⟨hr⟩
    have hphi : ((q : ZMod r) ^ 2 + (q : ZMod r) + 1) = 0 := by
      have h0 : ((q ^ 2 + q + 1 : ℕ) : ZMod r) = 0 :=
        (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
      push_cast at h0
      exact h0
    have hq3 : (q : ZMod r) ^ 3 = 1 := by
      calc (q : ZMod r) ^ 3
          = ((q : ZMod r) - 1) * ((q : ZMod r) ^ 2 + (q : ZMod r) + 1) + 1 := by ring
        _ = 1 := by rw [hphi]; ring
    have hq1 : (q : ZMod r) ≠ 1 := by
      intro h1
      rw [h1] at hphi
      have h3 : (3 : ZMod r) = 0 := by linear_combination hphi
      have hdvd3 : r ∣ 3 := (ZMod.natCast_zmod_eq_zero_iff_dvd 3 r).mp (by exact_mod_cast h3)
      have hle : r ≤ 3 := Nat.le_of_dvd (by decide) hdvd3
      have hge : 2 ≤ r := hr.two_le
      interval_cases r <;> norm_num at h3
    have hord_dvd : orderOf (q : ZMod r) ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
    have hord_ne1 : orderOf (q : ZMod r) ≠ 1 := by
      rw [orderOf_eq_one_iff]; exact hq1
    have hord_eq3 : orderOf (q : ZMod r) = 3 := by
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hord_dvd with h1 | h3
      · exact absurd h1 hord_ne1
      · exact h3
    have hq_ne0 : (q : ZMod r) ≠ 0 := by
      intro h0; rw [h0] at hq3; norm_num at hq3
    have hfermat : (q : ZMod r) ^ (r - 1) = 1 := ZMod.pow_card_sub_one_eq_one hq_ne0
    have h3_dvd : 3 ∣ r - 1 := by
      rw [← hord_eq3]
      exact orderOf_dvd_of_pow_eq_one hfermat
    omega

end Opn.Steuerwald
