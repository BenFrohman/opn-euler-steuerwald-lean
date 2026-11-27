# Status

**Machine-checked formalization of Steuerwald’s theorem (1937) and the associated cyclotomic divisibility lemma; existence of an odd perfect number remains open.**

## Formalized here
- Euler form structure
- Cyclotomic divisibility lemma (order argument in `ZMod`)
- Steuerwald 1937 (ordinary exponents all exactly 2) via short factor chain and 3-adic valuation

Remaining local gaps are elementary and finite (explicit expansion of the order argument and the factor chain). They do not rely on external certificates and use only standard Mathlib lemmas.

## Not formalized here (already available elsewhere)
- Equal-exponent exclusion for `3 ≤ r ≤ 83` (mathdiscoveries.org Lean library, standard axioms)
- Equal-exponent exclusion for `89 ≤ r ≤ 167` (certificates)
- Schorvitz (Nov 2026) bound `e^{59}` on the smallest prime factor under low ordinary exponents
- Absolute lower bounds on `N`

## Axioms
Once the elementary steps are fully expanded, `#print axioms` on the main theorems reports only the standard Lean axioms.
