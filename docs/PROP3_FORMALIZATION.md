# Proposition 3.2 formalization roadmap

This branch aims to formalize the complete logical proof of Proposition 3.2 of
*Normality in Mahler's Class of T-Numbers*, starting from the manuscript's
stated algebraic-approximation inputs.

**Completed on `prop3-full`: Phases 1 and 2, and the complete height-range
overlap/coverage argument.** The full proposition remains pending;
`PropositionThreeTwo.lean` has not been created.

## Scope boundary

The goal is to formalize Proposition 3.2 **from** the stated Section 2 inputs
and the elementary finiteness fact needed for the exponent bridge:

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
the external algebraic inputs. The actual scale-gap estimate is now derived
in `HeightRangeCoverage`. A concrete instance verifying all schedule fields
from the manuscript construction is not yet formalized.

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

### 3. HeightRangeCoverage.lean — completed

The module defines `CriterionSchedule.usableExponent`, `heightLeft`, and
`heightRight`, representing `u_{k,n}` and the interval endpoints in (3.18).
It reuses `K`, `aCoeff`, and `delta` from `DiophantineBudget`, and proves that
this delta is exactly the manuscript formula (3.16). Both delta positivity
and usable-exponent positivity at admissible stages are certified.

The actual scale-gap estimate (3.6) is derived from `scale_recurrence`,
`eventual_next_admissible`, and the existing `ScheduleBudget` lemmas. The
proof distinguishes one-step and two-step gaps, explicitly iterates the
recurrence to `Q(k+2) = Q(k)^(10000 A_k A_{k+1})`, bounds the skipped degree,
and converts the natural power to the real exponent `a_n A_k`.

Both inequalities of (3.17) are proved, including the intermediate endpoint
`Q(k)^(A_k/(4(n+2)))`, using the existing `overlap_budget`. Overlap is not
assumed by any input field. Degree recurrence at exact degree `n+1` yields
infinitely many admissible stages and an admissible stage beyond every
index. Positive delta and scale divergence yield eventual strict growth past
any real height, including at arbitrarily late admissible stages.

`exists_last_admissible_pair` constructs the last admissible stage whose left
endpoint is at most H. Divergence bounds all eligible indices; the initial
admissible stage makes this set nonempty. `Nat.findGreatest` supplies its
last index, and `Nat.find` supplies the least admissible index above it.
Maximality gives `left(k) ≤ H < left(k')`; minimality of the next index
establishes consecutive admissibility.

`exists_height_cover` proves, for every positive target degree and **every**
prescribed stage threshold N:

    ∃ H₀ ≥ 2, ∀ H ≥ H₀, ∃ k ≥ N,
      d_k > n ∧ Q(k)^delta_n ≤ H ∧ H ≤ Q(k)^u_{k,n}.

It chooses an initial stage beyond both N and the derived overlap threshold,
then applies the constructed consecutive pair and `height_in_current_range`.
The threshold is independent of x and of the target algebraic number.

All new theorem declarations are in namespace `TNumbersLean.CriterionSchedule`
and are listed in `scripts/Audit.lean`:

- `scheduleCoeff_cast`;
- `height_delta_eq`;
- `height_delta_pos`;
- `scale_pos`;
- `scale_ge_one`;
- `scale_strictMono`;
- `heightLeft_strictMono`;
- `usableExponent_pos`;
- `scale_two_step`;
- `consecutive_stage_cases`;
- `consecutive_scale_gap_nat`;
- `scale_gap_power_eq`;
- `exists_eventual_scale_gap`;
- `height_overlap_of_scale_gap`;
- `exists_eventual_height_overlap`;
- `admissible_infinite`;
- `exists_admissible_ge`;
- `heightLeft_tends_to_infinity`;
- `eventually_heightLeft_gt`;
- `exists_admissible_heightLeft_gt`;
- `exists_last_admissible_pair`;
- `exists_height_cover`.

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

## Validation of height-range coverage

- `lake build`: passed (7360 jobs).
- `bash scripts/check.sh`: passed, including all source checks and the full
  audit with `warningAsError=true`.
- The required project placeholder/custom-axiom search returned no output
  (exit status 1, meaning no matches).
- `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`
  for each of the 22 new theorems, including `exists_eventual_scale_gap`,
  `exists_eventual_height_overlap`, `exists_last_admissible_pair`, and
  `exists_height_cover`.
- No manuscript file was modified; no `PropositionThreeTwo.lean` was created.

## Adversarial statement audit

- (3.6): the eventual theorem quantifies over every consecutive admissible
  pair after a derived threshold and returns both the one/two-step index
  cases and the real-power scale inequality. This inequality is not a field.
- (3.16): `height_delta_eq` identifies the existing delta with exactly
  `1/(4 a_n (n+2))`; `height_delta_pos` proves positivity.
- (3.17): both inequalities are derived from (3.6) and the preexisting
  numerical reserve. No assumption contains the desired overlap conclusion.
- Recurrence: exact degree `n+1` is recurrent because `n ≥ 1`, and its stage
  set is contained in the admissible set. Infinitude implies unboundedness
  of this set in Nat; no extra late-stage existence hypothesis is used.
- Last stage: eligibility is nonempty at the chosen initial admissible stage
  and bounded above by eventual strict growth of the left endpoints.
  The greatest eligible stage and its next admissible stage are constructed.
- (3.18): every real H above the returned H₀ is covered, not just a
  subsequence. The covering stage is beyond any requested N and beyond the
  internally derived overlap threshold.
- Inequalities: `left(k) ≤ H < left(k') ≤ right(k)` implies the weak upper
  inequality required for applying (3.14), including interval boundaries.
- Monotonicity: `scale_strictMono` and `heightLeft_strictMono` prove the
  manuscript's increasing-endpoint assertion. The coverage construction
  itself uses divergence and maximality, so does not silently assume it.

## Remaining work for the complete proposition

No new mathematical input assumptions were introduced. The existing
`CriterionSchedule` construction hypotheses and the explicit Section 2 /
Northcott fields remain the boundary of the conditional formalization.
A concrete manuscript schedule satisfying all those schedule fields is still
needed to connect to the fully specified construction.

The Proposition 3.2 proof still needs local separation and the error comparison
(3.12)--(3.15), transcendence, the conversion of covered height ranges to the
global algebraic lower bound (3.19), and the recurrent-center argument giving
infinitely many distinct strong approximants. Then derive the explicit
upper/lower Koksma bounds, normalized growth, and T-number conclusion with the
existing bridges. The height-range coverage step is now complete. This run
deliberately stops before `PropositionThreeTwo.lean`.
