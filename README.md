# Odd Perfect Numbers: Euler Form, Steuerwald, and Cyclotomic Lemmas

Lean 4 + Mathlib formalization of classical necessary conditions on odd perfect numbers.

## Contents
- `IsOddPerfect` and `EulerForm`
- Cyclotomic divisibility lemma: primes dividing `eval q (cyclotomic r ℤ)` are `r` or `≡ 1 (mod r)`
- Steuerwald 1937: no odd perfect number with all ordinary exponents exactly 2

## Status
Existence of an odd perfect number remains open. These are necessary conditions only.

The equal-exponent exclusion for `3 ≤ r ≤ 83` is already machine-verified in the independent library at mathdiscoveries.org / github.com/mathdiscoveries/odd-perfect-equal-exponents.

## Build
```
lake build
```

## Axioms
All theorems depend only on standard Lean axioms.
