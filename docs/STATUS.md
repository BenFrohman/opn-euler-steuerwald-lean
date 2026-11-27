# Status

**Claim:** Machine-checked formalization of Steuerwald’s theorem (1937) and the associated cyclotomic lemma; existence of an odd perfect number remains open.

## External related results (November 2026)

These results are not formalized in this repository. They are cited for context.

- **Schorvitz (2026)**: If every ordinary prime factor of an odd perfect number has exponent 2 or 4, then the smallest prime factor is at most \(e^{59} \approx 4.2 \times 10^{25}\). This improves the prior bound of \(10^{1000}\) for this restricted family. Uniqueness: fixing the Euler prime power determines at most one such number. Unrefereed note; paper and verifier at https://schorvitz.com/opn-e59.zip and https://www.alphaxiv.org/abs/2611.odd-perfect-numbers-valuation-sieve.

- **Ochem lower bounds**: Published bound \(N > 10^{1500}\) (Ochem–Rao 2012). Computational extensions report \(N > 10^{2200}\) on Ochem’s project page (https://www.lirmm.fr/~ochem/opn/). The growth of the absolute lower bound remains limited by unfactored composite roadblocks arising from factor chains on \(\sigma(q^a)\).

- **Equal-exponent cases (mathdiscoveries.org)**: Exclusion of equal ordinary exponents through \(r \le 167\) (Lean-verified through \(r = 83\), certificates thereafter).

## What this repository formalizes

Only the classical Steuerwald theorem (all ordinary exponents exactly 2 is impossible) and the supporting cyclotomic divisibility lemma. No new quantitative bounds are claimed.
