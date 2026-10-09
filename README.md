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
| Theorem 1.1, Fourier second moment | [FourierSecondMoment.lean](TNumbersLean/FourierSecondMoment.lean) | Verified |
| Theorem 1.1, summable off-diagonal tail | [FourierTailSummability.lean](TNumbersLean/FourierTailSummability.lean) | Verified |
| Theorem 1.1, Chebyshev and Borel--Cantelli | [FourierBorelCantelli.lean](TNumbersLean/FourierBorelCantelli.lean) | Verified |
| Theorem 1.1, interpolation from squares to all indices | [WeylInterpolation.lean](TNumbersLean/WeylInterpolation.lean) | Verified |
| Theorem 1.1, all bases and frequencies | [WeylAlmostEverywhere.lean](TNumbersLean/WeylAlmostEverywhere.lean) | Verified from the Fourier-decay hypothesis |
| Theorem 1.1, packet support to arithmetic witnesses | [PacketSupport.lean](TNumbersLean/PacketSupport.lean), [PacketSupportSet.lean](TNumbersLean/PacketSupportSet.lean) | Verified |
| Theorem 1.1, stretched Fourier profile tends to zero | [FourierDecayLimits.lean](TNumbersLean/FourierDecayLimits.lean) | Verified |
| Theorem 1.1, total mass perturbation and $15/16$--$17/16$ bounds | [MeasureMassBudget.lean](TNumbersLean/MeasureMassBudget.lean) | Verified |
| Theorem 1.1, perfect-set assembly | [TheoremOneOneAssembly.lean](TNumbersLean/TheoremOneOneAssembly.lean) | Verified from positive arithmetic mass and Fourier decay |
| Theorem 1.1(i), paper-facing arithmetic/normality assembly | [TheoremOneOnePartOne.lean](TNumbersLean/TheoremOneOnePartOne.lean) | Verified from the measure-construction outputs |

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
| [FourierSecondMoment.lean](TNumbersLean/FourierSecondMoment.lean) | Exact Weyl second-moment identity and finite Fourier-decay bound |
| [FourierTailSummability.lean](TNumbersLean/FourierTailSummability.lean) | Summable lacunary off-diagonal majorant and uniform linear second moment |
| [FourierBorelCantelli.lean](TNumbersLean/FourierBorelCantelli.lean) | Chebyshev bound, summable bad sets, and square-subsequence Borel--Cantelli |
| [WeylInterpolation.lean](TNumbersLean/WeylInterpolation.lean) | Square-to-all-index interpolation for normalized Weyl sums |
| [WeylAlmostEverywhere.lean](TNumbersLean/WeylAlmostEverywhere.lean) | Countable intersection over all bases and nonzero integer frequencies |
| [PacketSupport.lean](TNumbersLean/PacketSupport.lean) | Prime-packet stage data imply the reduced witnesses used by `MemE` |
| [PacketSupportSet.lean](TNumbersLean/PacketSupportSet.lean) | Geometric manuscript packet set and its inclusion in the arithmetic construction set |
| [FourierDecayLimits.lean](TNumbersLean/FourierDecayLimits.lean) | Stretched-log Fourier decay implies Fourier/characteristic-function vanishing at infinity |
| [MeasureMassBudget.lean](TNumbersLean/MeasureMassBudget.lean) | Summable $2^{-k-4}$ mass-error budget and the $15/16$--$17/16$ bounds |
| [TheoremOneOneAssembly.lean](TNumbersLean/TheoremOneOneAssembly.lean) | Positive-mass arithmetic set plus Fourier normality gives a compact perfect subset |
| [TheoremOneOnePartOne.lean](TNumbersLean/TheoremOneOnePartOne.lean) | Paper-facing Theorem 1.1(i) assembly from compact packet support and measure inputs |

## Verification

The project is pinned to Lean 4.24.0 and mathlib v4.24.0.

```bash
lake exe cache get
bash scripts/check.sh
```

The audit builds every project module with warnings treated as errors, prints
the axioms of the principal declarations, and fails if any listed theorem
depends on `sorryAx`.

Formal proof commit: [`45485ed`](https://github.com/DiegoMarquesMath/TNumbersLean/tree/45485edceb96ea46879e8f4ab174f3f1d953bbcc).  
See [VALIDATION.md](VALIDATION.md) for the final verification record.

## Scope

The concrete schedule, actual rational algebraicity and degree, primitive
integer minimal polynomial naive height, elementary Northcott finiteness, and
approximation centers are formalized. Only the Section 2 height comparison
(2.2) and translated-center separation (Lemma 2.1) remain explicit mathematical
inputs in `SectionTwoInputs`. Schmidt's theorem and Icen's lemma themselves
are not reproved in Lean.

The analytic implication from the manuscript's Fourier-decay hypothesis to
simultaneous Weyl normality is now formalized: the development proves the
second-moment identity and linear bound, summability of the off-diagonal tail,
Chebyshev estimates, first Borel--Cantelli on square indices, interpolation to
all indices, and the countable intersection over all bases and nonzero integer
frequencies.  It also formalizes the final perfect-set extraction from any
positive-measure measurable arithmetic set for an atomless probability measure.

For a completely self-contained Lean proof of Theorem 1.1(i), the remaining
major analytic block is now sharply isolated.  The geometric support set of
the prime-denominator packets is formalized and is proved to imply the
concrete arithmetic condition `MemE`; the summable mass-error budget is also
formalized, including the manuscript bounds $15/16\le M\le17/16$.  Moreover,
the stated stretched-log Fourier decay is proved to force both
`paperFourier` and the mathlib characteristic function to vanish at positive
infinity.

What remains is the construction of the smooth packets and densities
$f_k=f_{k-1}G_k$, the packet Fourier/derivative estimate, passage to the
limiting probability measure with support in `manuscriptPacketSet`, and the
final deduction that the limiting measure is atomless.  Once these outputs
are supplied, `TheoremOneOnePartOne.lean` already assembles a nonempty compact
perfect subset of $J$ consisting of T-numbers satisfying the simultaneous Weyl
criterion in every base.

The project currently records absolute normality through the simultaneous
Weyl criterion `WeylAbsolutelyNormal`; translating this analytic criterion
to a digit-frequency definition of normality is also not separately
formalized.

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
