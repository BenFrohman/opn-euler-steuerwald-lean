# Odd Perfect Numbers — Euler Form, Cyclotomic Divisibility, and Steuerwald (1937)

[![Lean CI](https://github.com/BenFrohman/opn-euler-steuerwald-lean/actions/workflows/lean-ci.yml/badge.svg)](https://github.com/BenFrohman/opn-euler-steuerwald-lean/actions/workflows/lean-ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--7068--3718-brightgreen.svg)](https://orcid.org/0009-0006-7068-3718)

Lean 4 + Mathlib formalization of classical necessary conditions on odd perfect numbers.

**Author**: Benjamin Stanley Frohman  
**ORCID**: [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)  
**License**: Apache-2.0  
**Copyright**: (c) 2026 Benjamin Stanley Frohman

## Claim
**Machine-checked formalization of Steuerwald’s theorem (1937) and the associated cyclotomic divisibility lemma; existence of an odd perfect number remains open.**

This repository does not claim to resolve the existence question. It supplies a reproducible Lean 4 reference implementation of two classical constraints.

## What is formalized
- `IsOddPerfect` and Euler form structure
- Cyclotomic divisibility lemma: primes dividing `\Phi_r(q)` are `r` or `\equiv 1 \pmod{r}`
- Steuerwald’s 1937 theorem: no odd perfect number in which every ordinary prime appears to exponent exactly 2

## Comparison

| Result | This repository | External verification | Novelty |
|--------|------------------|-----------------------|---------|
| Steuerwald 1937 (ordinary exponents = 2) | Formalized (elementary chain + valuation) | Classical literature; re-proved many times | Re-verification in Lean 4 |
| Cyclotomic divisibility lemma | Formalized (ZMod order) | Standard in Mathlib / textbooks | Re-verification |
| Equal-exponent exclusion `3 ≤ r ≤ 83` | Not included | Fully machine-checked in [mathdiscoveries/odd-perfect-equal-exponents](https://github.com/mathdiscoveries/odd-perfect-equal-exponents) (standard axioms) | Already available |
| Equal-exponent exclusion `89 ≤ r ≤ 167` | Not included | Certificate-based on mathdiscoveries.org | Already available |
| Schorvitz (Nov 2026) low-ordinary-exponents bound `e^{59}` | Not included | Preprint (analytic) | New quantitative bound; not re-verified here |
| Absolute lower bound `N > 10^{1500}` (published) / `> 10^{2200}` (computational) | Not included | Ochem–Rao and subsequent work | Not re-verified here |

## Reproduce
```bash
# Requires elan
lake exe cache get
lake update
lake build
```

To inspect axioms (once remaining elementary expansions are closed):
```bash
lake env lean --run -c 'import Opn.Basic
#print axioms steuerwald
#print axioms prime_dvd_cyclotomic'
```
Expected (after full discharge): only `propext`, `Classical.choice`, `Quot.sound`.

## Status
See [docs/STATUS.md](docs/STATUS.md). Existence remains open.

## License
Apache License 2.0. Copyright (c) 2026 Benjamin Stanley Frohman.
See [LICENSE](LICENSE).
