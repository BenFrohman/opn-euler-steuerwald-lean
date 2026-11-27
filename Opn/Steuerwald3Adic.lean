import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

open scoped ArithmeticFunction BigOperators

namespace OPN

/-- Elementary mod-3 lemma: if `3 ∤ q`, then `3 ∣ 1 + q + q^2` (i.e. `3 ∣ Φ₃(q)`). -/
lemma three_dvd_phi3 {q : ℕ} (hq3 : ¬ 3 ∣ q) : 3 ∣ (1 + q + q ^ 2) := by
  have hmod : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hmod with h1 | h2
  · have : (1 + q + q ^ 2) % 3 = 0 := by
      calc (1 + q + q ^ 2) % 3
          = (1 + (q % 3) + (q % 3) ^ 2) % 3 := by simp [Nat.add_mod, Nat.pow_mod]
        _ = (1 + 1 + 1 ^ 2) % 3 := by rw [h1]
        _ = 0 := by norm_num
    exact Nat.dvd_of_mod_eq_zero this
  · have : (1 + q + q ^ 2) % 3 = 0 := by
      calc (1 + q + q ^ 2) % 3
          = (1 + (q % 3) + (q % 3) ^ 2) % 3 := by simp [Nat.add_mod, Nat.pow_mod]
        _ = (1 + 2 + 2 ^ 2) % 3 := by rw [h2]
        _ = 0 := by norm_num
    exact Nat.dvd_of_mod_eq_zero this

/-- Product over a Finset of elements each divisible by `3` is divisible by `3 ^ s.card`. -/
lemma three_pow_card_dvd_prod {α : Type*} (s : Finset α) (f : α → ℕ)
    (hf : ∀ x ∈ s, 3 ∣ f x) :
    3 ^ s.card ∣ ∏ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.card_insert_of_not_mem ha, Finset.prod_insert ha, pow_succ']
    exact mul_dvd_mul (hf a (Finset.mem_insert_self a s))
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

/-- Structure representing a hypothetical odd perfect number in Steuerwald form. -/
structure SteuerwaldCandidate where
  p : ℕ
  α : ℕ
  Q : Finset ℕ
  hp : Nat.Prime p
  hp4 : p % 4 = 1
  hα4 : α % 4 = 1
  hQ_nonempty : Q.Nonempty
  hQ_prime : ∀ q ∈ Q, Nat.Prime q
  hQ_odd : ∀ q ∈ Q, Odd q
  hp_not_mem : p ∉ Q
  h_perfect : σ 1 (p ^ α * ∏ q ∈ Q, q ^ 2) = 2 * (p ^ α * ∏ q ∈ Q, q ^ 2)

end OPN
