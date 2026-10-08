# Proposition 3.2 formalization roadmap

This branch aims to formalize the complete logical proof of Proposition 3.2 of
*Normality in Mahler's Class of T-Numbers*, starting from the manuscript's
stated algebraic-approximation inputs.

**Completed on `prop3-full`: Phases 1 and 2 only.** The full proposition
remains pending; `PropositionThreeTwo.lean` has not been created.

## Scope boundary

The goal is to formalize Proposition 3.2 **from** the two inputs already isolated
in Section 2:

1. the translated-center separation supplied by Lemma 2.1;
2. exact degree and the two-sided height comparison for the recurrent centers
   in (2.2);
3. elementary Northcott finiteness for bounded degree and bounded naive height.

The project does not attempt to formalize Schmidt's theorem itself or Icen's
height lemma at this stage.

## Target theorem

For a point satisfying the criterion defining E(J;Q_1), prove in Lean:

- transcendence;
- the uniform large-height lower bound (3.10);
- finite upper bounds for every fixed Koksma exponent;
- exact-degree recurrent lower bounds;
- divergence of the normalized fixed-degree lower bounds;
- the T-number conclusion.

The formal statement should mirror the manuscript as closely as practical.

## Planned modules

### 1. KoksmaExponent.lean — completed

`AlgebraicApproximationSystem` supplies `isAlg`, `degree`, `height`, positive
algebraic degree, height at least one, and bounded-degree/bounded-height
Northcott finiteness. Algebraicity and transcendence are relative to this
interface; no concrete naive-height implementation or external theorem is
asserted by Lean.

`approximants` encodes exactly `0 < |x - α| < H(α)^(-w-1)` with degree at
most `n`. `admissibleExponents` requires this set of real values to be
infinite, so repeated witnesses or stage indices cannot replace distinct
approximants. `wStar` is its extended-real supremum, including the empty
and unbounded cases. `normalizedWStar` divides by the degree; degree zero
does not affect the filter at infinity.

`IsTNumber` uses transcendence, `wStar < ⊤` at every positive degree, and
`Filter.limsup normalizedWStar Filter.atTop = ⊤`, exactly the formulation
of (1.2). Certified declarations in namespace
`TNumbersLean.AlgebraicApproximationSystem`:

- `admissible_le_wStar`;
- `upper_bound_bridge`: an eventual height lower bound bounds `wStar`;
  the proof explicitly uses Northcott to make all bounded-height exceptions
  finite, and uses real-power monotonicity above the threshold;
- `lower_bound_bridge`: infinitude for every real `w < W` gives `W ≤ wStar`;
- `t_number_bridge`: transcendence, fixed-degree upper finiteness, and
  unbounded normalized exponents on every tail imply the limsup criterion;
- `isTNumber_iff_tail_unbounded`: proves equivalence with that tail formulation.

### 2. CriterionInputs.lean — completed

`CriterionSchedule` records zero-indexed stage data `Q`, `d`, `A`, the scale
recurrence, the cubic stage exponent, divergence of scales, recurrent degrees,
and eventual availability of an admissible stage within the next two stages.
These are construction hypotheses corresponding to Lemma 3.1, separate from
the external algebraic inputs. A concrete schedule instance and the remaining
schedule verification are not yet formalized.

`CriterionInputs S schedule x` records selected centers and denominators,
the denominator block, the original q-based source approximation (3.8),
algebraicity and exact degree, the two-sided q-based height comparison (2.2)
with one constant per degree, and translated-center separation from Lemma 2.1
at admissible stages. Separation is specialized to the selected centers after
the threshold condition has been discharged. The reduced-translation origin
of the centers is abstracted by the supplied degree and height bounds.
Northcott remains in `AlgebraicApproximationSystem` rather than being duplicated.

No global lower bound, transcendence, Koksma bound, or T-number conclusion is
assumed by either input structure. Certified declarations in namespace
`TNumbersLean.CriterionInputs`:

- `source_approximation_Q`: deduces the Q-based source bound from (3.8);
- `admissible_exponent_lower`: deduces the admissible cubic reserve using
  `TNumbersLean.stageExponent_le_of_degree_le` from `ScheduleBudget`;
- `usable_exponent_lower`: applies the existing Diophantine budget to obtain
  the usable exponent reserve in (3.15).

The module imports `DiophantineBudget`, `ScheduleBudget`, and `HeightOverlap`;
no existing numerical lemma is duplicated.

### 3. HeightRangeCoverage.lean

Formalize the overlap argument (3.16)--(3.18), including the
last-admissible-stage step for all sufficiently large heights.

### 4. PropositionThreeTwo.lean

Formalize:

- (3.12)--(3.15);
- transcendence;
- (3.16)--(3.19);
- the bound w_n^*(x) <= B_n;
- strong approximation at each recurrent degree;
- w_d^*(x) >= (d+1)^3/d - 1;
- w_d^*(x)/d -> infinity;
- the final T-number criterion.

## Quality requirements

No placeholders or custom unproved axioms are permitted.

Every project declaration used to certify Proposition 3.2 must be listed in
scripts/Audit.lean.

After each module, both

    lake build
    bash scripts/check.sh

must pass.

The final README and validation record must distinguish clearly between
formalized manuscript arguments and external Section 2 inputs assumed by the
formal interface.

## Validation of Phases 1 and 2

- `lake build`: passed (7359 jobs).
- `bash scripts/check.sh`: passed, including every project module and the
  axiom audit with `warningAsError=true`.
- `grep -RInE '\b(sorry|admit)\b|^[[:space:]]*axiom\b' TNumbersLean scripts`:
  no output (exit status 1, meaning no matches).
- Every new certification theorem is listed in `scripts/Audit.lean`.
- `#print axioms` for all eight new theorems reports exactly
  `[propext, Classical.choice, Quot.sound]`.
- The manuscript `.tex` and `.pdf` were not modified.

## Remaining work for the complete proposition

Instantiate/verify the manuscript schedule, prove height-range coverage and
the local/global separation bounds, derive transcendence, and turn recurrent
centers into infinitely many distinct strong approximants using their growing
heights. Then prove the explicit upper/lower exponent bounds and normalized
asymptotics, and apply the completed Koksma bridges. These are future phases;
this run deliberately stops before `PropositionThreeTwo.lean`.
