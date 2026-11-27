## Claim

Machine-checked formalization in Lean 4 + Mathlib of **Steuerwald’s theorem (1937)** (`steuerwald_1937`) and its immediate **fourth-power corollary** (`exists_ordinary_exponent_ge_two_of_odd_perfect`): any odd perfect number in Euler form $N = p^\alpha \prod q_i^{2\beta_i}$ must satisfy $\beta_i \ge 2$ (i.e., $q_i^4 \mid N$) for at least one ordinary prime $q_i$. **Existence of an odd perfect number remains open.**

## Verified Theorems (`Opn/Basic.lean`)

- `steuerwald_1937`: No odd perfect number has the form $N = p^\alpha \prod q_i^2$.
- `exists_ordinary_exponent_ge_two_of_odd_perfect`: Every odd perfect number in EulerForm has at least one ordinary prime $q_i$ with $\beta_i \ge 2$.
- `#print axioms` reports only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) with zero sorrys.
