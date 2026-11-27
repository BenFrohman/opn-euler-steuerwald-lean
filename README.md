# Odd Perfect Numbers — Euler Form, Cyclotomic Divisibility, and Steuerwald (1937)

[![Lean CI](https://github.com/BenFrohman/opn-euler-steuerwald-lean/actions/workflows/lean-ci.yml/badge.svg)](https://github.com/BenFrohman/opn-euler-steuerwald-lean/actions/workflows/lean-ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--7068--3718-brightgreen.svg)](https://orcid.org/0009-0006-7068-3718)

Lean 4 + Mathlib formalization of classical necessary conditions on odd perfect numbers.

**Author**: Benjamin Stanley Frohman  
**ORCID**: [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)  
**License**: Apache-2.0  
**Copyright**: (c) 2026 Benjamin Stanley Frohman

## Status
**Existence of an odd perfect number remains open.**  
This repository formalizes only proven classical constraints (Euler form, cyclotomic divisibility, Steuerwald 1937).

The equal-exponent exclusion for all odd primes \(3 \le r \le 83\) is already machine-checked (standard axioms only) in the independent library [mathdiscoveries/odd-perfect-equal-exponents](https://github.com/mathdiscoveries/odd-perfect-equal-exponents).

## What is formalized
- `IsOddPerfect` and Euler form structure
- Cyclotomic divisibility lemma: primes dividing `\Phi_r(q)` are `r` or `\equiv 1 \pmod{r}`
- Steuerwald’s 1937 theorem: no odd perfect number in which every ordinary prime appears to exponent exactly 2

## Reproduce
```bash
# Requires elan
lake exe cache get
lake update
lake build
```

To inspect axioms (once remaining elementary steps are closed):
```bash
lake env lean --run -c 'import Opn.Basic
#print axioms steuerwald
#print axioms prime_dvd_cyclotomic'
```

## License
Apache License 2.0. Copyright (c) 2026 Benjamin Stanley Frohman.
See [LICENSE](LICENSE).
