# Normality in Mahler's Class of T-Numbers

[![Lean verification](https://github.com/DiegoMarquesMath/TNumbersLean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/DiegoMarquesMath/TNumbersLean/actions/workflows/lean.yml)

Lean 4 formalization accompanying Diego Marques's manuscript  
*Normality in Mahler's Class of T-Numbers*.

The development formalizes the common Diophantine criterion of the paper and
machine-checks selected quantitative steps from the Fourier and digit-block
constructions.

## Proposition 3.2

The main declaration is

[`TNumbersLean.concrete_proposition_three_two`](TNumbersLean/ConcretePropositionThreeTwo.lean).

The proof of Proposition 3.2 is formally verified in Lean 4 from the stated
Section 2 algebraic-approximation inputs. For points in the manuscript's
$E(J;Q_1)$, it proves:

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
| Lemma 3.1 / (3.1)--(3.5), concrete degree schedule | [ConcreteSchedule.lean](TNumbersLean/ConcreteSchedule.lean) | Verified from threshold data |
| Lemma 3.1 / (3.6), bounded scale gaps | [ScheduleBudget.lean](TNumbersLean/ScheduleBudget.lean), [HeightRangeCoverage.lean](TNumbersLean/HeightRangeCoverage.lean) | Verified |
| Actual algebraic degree, naive height, and Northcott | [ConcreteAlgebraicData.lean](TNumbersLean/ConcreteAlgebraicData.lean) | Verified |
| Proposition 3.2, Koksma framework | [KoksmaExponent.lean](TNumbersLean/KoksmaExponent.lean) | Verified |
| Proposition 3.2, Section 2 input interface | [CriterionInputs.lean](TNumbersLean/CriterionInputs.lean) | Verified interface |
| E witnesses and concrete centers | [ConcreteCriterionInputs.lean](TNumbersLean/ConcreteCriterionInputs.lean) | Verified from Section 2 inputs |
| Proposition 3.2, concrete final theorem | [ConcretePropositionThreeTwo.lean](TNumbersLean/ConcretePropositionThreeTwo.lean) | Verified from Section 2 inputs |
| Lemma 5.1, perturbation budget | [FourierBudget.lean](TNumbersLean/FourierBudget.lean) | Verified calculation |
| Sections 7--8, digit-block constants | [DigitBudget.lean](TNumbersLean/DigitBudget.lean) | Verified calculation |

The concrete schedule is `ScheduleThresholds.concreteCriterionSchedule`;
`ScheduleThresholds.lemma_three_one` collects its manuscript properties. It
assumes only the external integer thresholds and the initial scale. Lean stage
`k` is manuscript stage `k+1`. The actual algebraic system is
`realAlgebraicApproximationSystem`; `concreteCriterionInputs` constructs the
centers from reduced witnesses in $E(J;Q_1)$.

The exact theorem correspondence and external scope are recorded in
[docs/PROPOSITION_3_2.md](docs/PROPOSITION_3_2.md).

## Repository map

| File | Purpose |
| --- | --- |
| [KoksmaExponent.lean](TNumbersLean/KoksmaExponent.lean) | Koksma exponents, Northcott bridge, and T-number criterion |
| [ConcreteAlgebraicData.lean](TNumbersLean/ConcreteAlgebraicData.lean) | Actual real algebraicity, degree, primitive minimal polynomial naive height, and elementary Northcott |
| [ConcreteSchedule.lean](TNumbersLean/ConcreteSchedule.lean) | Concrete recursive integer schedule and proved CriterionSchedule instance |
| [ConcreteCriterionInputs.lean](TNumbersLean/ConcreteCriterionInputs.lean) | Reduced E witnesses, actual centers, and explicit Section 2 inputs |
| [ConcretePropositionThreeTwo.lean](TNumbersLean/ConcretePropositionThreeTwo.lean) | Concrete Proposition 3.2 and paper-facing corollaries |
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

See [VALIDATION.md](VALIDATION.md) for the final verification record.

## Scope

The concrete schedule, actual rational algebraicity and degree, primitive
integer minimal polynomial naive height, elementary Northcott finiteness, and
approximation centers are formalized. Only the Section 2 height comparison
(2.2) and translated-center separation (Lemma 2.1) remain explicit mathematical
inputs in `SectionTwoInputs`. Schmidt's theorem and Icen's lemma themselves
are not reproved in Lean.

The full Fourier-measure argument, Weyl/Borel--Cantelli step, and complete
digit-block Cantor construction are outside the current formalization.

## Citation

Suggested manuscript wording:

> A Lean 4 formal verification of Proposition 3.2, including the concrete
> degree schedule, the actual algebraic degree and naive height, and the
> construction of the approximation centers, is available at
> https://github.com/DiegoMarquesMath/TNumbersLean.
> The Section 2 separation and height-comparison results are used as
> external mathematical inputs.

Português: [guia rápido](docs/GUIA_PT.md).  
Maintained by [Diego Marques](https://github.com/DiegoMarquesMath).
