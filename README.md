# Normality in Mahler's Class of T-Numbers

[![Lean verification](https://github.com/DiegoMarquesMath/TNumbersLean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/DiegoMarquesMath/TNumbersLean/actions/workflows/lean.yml)

Lean 4 formalization accompanying Diego Marques's manuscript  
*Normality in Mahler's Class of T-Numbers*.

The development formalizes the common Diophantine criterion of the paper and
machine-checks selected quantitative steps from the Fourier and digit-block
constructions.

## Proposition 3.2

The main declaration is

[`TNumbersLean.proposition_three_two`](TNumbersLean/PropositionThreeTwo.lean).

From the explicit `CriterionSchedule` and `CriterionInputs` interfaces, Lean proves
the complete logical content of Proposition 3.2:

- transcendence of the constructed point;
- uniform exclusion of algebraic numbers of bounded degree at all sufficiently large heights;
- the explicit upper bound $w_n^*(x)\le B_n$;
- recurrent exact-degree approximants and
  $$
  w_d^*(x)\ge \frac{(d+1)^3}{d}-1;
  $$
- divergence of the normalized exponents;
- the T-number conclusion.

The proof includes the full height-range argument

$$
Q_k^{\delta_n}\le H\le Q_k^{u_{k,n}}
$$

for every sufficiently large real height $H$, rather than only along selected scales.

## Correspondence with the manuscript

| Manuscript | Lean source | Status |
| --- | --- | --- |
| Lemma 3.1 / (3.6), bounded scale gaps | [ScheduleBudget.lean](TNumbersLean/ScheduleBudget.lean), [HeightRangeCoverage.lean](TNumbersLean/HeightRangeCoverage.lean) | Verified |
| Proposition 3.2, Koksma framework | [KoksmaExponent.lean](TNumbersLean/KoksmaExponent.lean) | Verified |
| Proposition 3.2, Section 2 input interface | [CriterionInputs.lean](TNumbersLean/CriterionInputs.lean) | Verified interface |
| Proposition 3.2, (3.12)--(3.20) and final assembly | [PropositionThreeTwo.lean](TNumbersLean/PropositionThreeTwo.lean) | Verified from interfaces |
| Lemma 5.1, perturbation budget | [FourierBudget.lean](TNumbersLean/FourierBudget.lean) | Verified calculation |
| Sections 7--8, digit-block constants | [DigitBudget.lean](TNumbersLean/DigitBudget.lean) | Verified calculation |

The exact scope and the remaining concrete-instantiation work are recorded in
[docs/PROPOSITION_3_2.md](docs/PROPOSITION_3_2.md).

## Repository map

| File | Purpose |
| --- | --- |
| [KoksmaExponent.lean](TNumbersLean/KoksmaExponent.lean) | Koksma exponents, Northcott bridge, and T-number criterion |
| [CriterionInputs.lean](TNumbersLean/CriterionInputs.lean) | Abstract interface for the schedule, centers, degree, height, and Section 2 separation |
| [HeightRangeCoverage.lean](TNumbersLean/HeightRangeCoverage.lean) | Scale gaps, overlap, and coverage of all sufficiently large heights |
| [PropositionThreeTwo.lean](TNumbersLean/PropositionThreeTwo.lean) | Complete logical proof of Proposition 3.2 from the interfaces |
| [FourierBudget.lean](TNumbersLean/FourierBudget.lean) | Fourier perturbation estimates |
| [DigitBudget.lean](TNumbersLean/DigitBudget.lean) | Numerical bounds in the digit-block construction |

## Verification

The project is pinned to Lean 4.24.0 and mathlib v4.24.0.

```bash
lake exe cache get
bash scripts/check.sh
```

The audit builds every project module with warnings treated as errors, prints
the axioms of the principal declarations, and fails if any listed theorem
depends on `sorryAx`.

For the Proposition 3.2 proof commit
[`05cb79aa572d156674c562ae0dd0120a5ae15a36`](https://github.com/DiegoMarquesMath/TNumbersLean/tree/05cb79aa572d156674c562ae0dd0120a5ae15a36):

- `lake build` passed with 7361 jobs;
- `scripts/check.sh` passed;
- the placeholder/custom-axiom search returned no matches;
- the 29 new audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

See [VALIDATION.md](VALIDATION.md) for the compact validation record.

## Scope

At present, Proposition 3.2 is formally proved **from explicit interfaces**
encoding the schedule and the algebraic-approximation data used in the manuscript.

Still to be instantiated concretely are the schedule (3.1)--(3.3), real
algebraic degree and naive height, Northcott finiteness, and the centers arising
from membership in $E(J;Q_1)$. Schmidt's theorem and Icen's height lemma remain
external mathematical inputs, as in the paper.

The full Fourier-measure argument, Weyl/Borel--Cantelli step, and complete
digit-block Cantor construction are outside the current formalization.

## Citation

Current manuscript wording:

> A Lean 4 formal verification of the common Diophantine criterion,
> including the complete proof of Proposition 3.2 from its stated
> algebraic-approximation and schedule interfaces, together with selected
> quantitative checks in the Fourier and digit-block constructions, is
> available in the TNumbersLean repository.

Português: [guia rápido](docs/GUIA_PT.md).  
Maintained by [Diego Marques](https://github.com/DiegoMarquesMath).
