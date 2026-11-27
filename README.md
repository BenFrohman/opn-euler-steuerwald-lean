# Odd Perfect Numbers: Euler Form and Steuerwald Formalization

A Lean 4 + Mathlib formalization of classical necessary conditions on odd perfect numbers.

## Status

**The existence of an odd perfect number remains an open problem.**

This repository formalizes:
- The definition of an odd perfect number (`IsOddPerfect`)
- Euler's form (`EulerForm`)
- The cyclotomic divisibility lemma for primes dividing `Φ_r(q)`
- Steuerwald's 1937 theorem: there is no odd perfect number in which every ordinary exponent is exactly 2

The equal-exponent exclusion results for `3 ≤ r ≤ 83` are independently machine-checked in [mathdiscoveries/odd-perfect-equal-exponents](https://github.com/mathdiscoveries/odd-perfect-equal-exponents).

## Building

Requires [elan](https://github.com/leanprover/elan) and a working Lean 4 installation.

```bash
git clone https://github.com/BenFrohman/opn-euler-steuerwald-lean.git
cd opn-euler-steuerwald-lean
lake update
lake build
```

To check axioms on the main theorems:
```bash
lake env lean Opn/Basic.lean
# then in the REPL or file:
# #print axioms steuerwald
```

All proofs rely only on the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Structure

- `Opn/Basic.lean` — core definitions and theorems
- `lakefile.lean` — package configuration
- `lean-toolchain` — pinned Lean version

## License

Apache-2.0

Author: Benjamin Stanley Frohman
