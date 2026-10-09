# Proposition 3.2 — formalization record

This branch formalizes the complete logical proof of Proposition 3.2 of
*Normality in Mahler's Class of T-Numbers*, starting from the manuscript's
stated algebraic-approximation inputs.

**Completed:** the complete logical proof of Proposition 3.2 from the
interfaces, and, on `concrete-prop3`, the concrete integer schedule (3.1)--(3.3),
actual rational algebraicity and degree, primitive integer minimal polynomial
naive height, and elementary Northcott. `concreteCriterionInputs` now constructs the actual center inputs from
membership in E(J;Q_1), conditional only on the explicit Section 2 height and
separation consequences. The literal final theorem is `TNumbersLean.concrete_proposition_three_two`.

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

`TNumbersLean.proposition_three_two` now supplies all of these conclusions
from the declared interfaces, including the stronger normalized limit.
The connection from membership in the concrete E(J;Q_1) to those interfaces
is now `concreteCriterionInputs`, with only Section 2 estimates external.
The final literal proposition wrapper is `concrete_proposition_three_two`.

## Modules

### 1. KoksmaExponent.lean — completed

`AlgebraicApproximationSystem` supplies `isAlg`, `degree`, `height`, positive
algebraic degree, height at least one, and bounded-degree/bounded-height
Northcott finiteness. Algebraicity and transcendence are relative to this
interface in this module. `ConcreteAlgebraicData.lean` now supplies the actual
naive-height implementation and proves its Northcott field.

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
in `HeightRangeCoverage`. `ConcreteSchedule` now constructs an instance and
verifies all schedule fields from the manuscript recursion and the external
threshold data.

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

### 4. PropositionThreeTwo.lean — completed from the interfaces

`propositionB` defines exactly the real constant (3.9). `propositionB_eq`
reuses `B_exponent_identity` to identify it with `n+2+(K_n+1)/delta_n`.
`recurrentW` defines the real lower exponent `(d+1)^3/d-1`.

| Manuscript step | Certified declarations |
| --- | --- |
| (3.12), triangle estimate | `local_separation` |
| Error ratio and (3.14) | `source_error_factorization`, `source_error_ratio_bound`, `absorbed_local_bound` |
| Uniform positive reserve from (3.15) | `usableExponent_uniform_lower`, `eventually_admissible_heightRight_ge` |
| Transcendence | `transcendence` |
| (3.16)--(3.18) | The completed `HeightRangeCoverage` module is reused |
| (3.19), (3.10) | `covered_scale_factor`, `height_half_absorption`, `global_separation_uniform`, `global_separation` |
| Upper bound of (3.11) | `upper_wStar_bound`, `wStar_lt_top` |
| Distinct recurrent centers | `center_height_tends_to_infinity`, `recurrent_center_heights_unbounded`, `recurrent_centers_infinite` |
| Strict approximation of exact degree d | `eventually_recurrent_strong_approximation`, `recurrent_exact_approximants_infinite` |
| Lower bound of (3.11) | `recurrent_approximants_infinite`, `lower_wStar_bound` |
| (3.20) | `normalized_lower_bound`, `normalized_ge_degree`, `normalized_tail_unbounded`, `normalized_tends_to_top` |
| (1.2) and final proposition | `isTNumber`, `proposition_three_two` |

The ratio calculation proves both manuscript inequalities before absorbing
the source error. Transcendence uses a fixed positive lower bound for all
admissible usable exponents and scale divergence, then applies the local bound
to beta=x. No transcendence premise is introduced.

`global_separation_uniform` chooses H_n before quantifying over **every**
point-specific `CriterionInputs S s y` and every target beta. Thus the height
threshold is uniform in both y and beta for the fixed schedule. Its proof
uses the coverage theorem for all sufficiently large real heights, the
negative-power conversion of the left-endpoint bound, and H>=2 to absorb 1/2.
Northcott enters the upper exponent proof only through the existing bridge.

Center heights diverge by q>=Q, the height lower bound, and positive exact
stage degrees. A finite set of center values would have a finite, bounded set
of heights; recurrence supplies arbitrarily late centers violating that bound.
This proves infinitude of distinct values on every recurrent tail.

For every real w<W_d, strict approximation is proved eventually on that tail.
When w+1>=0, the positive exponent gap and the fixed degree-d height constant
provide the strict inequality. When w+1<0, height>=1 and the source bound
already make it strict. Positive approximation error uses the previously
proved transcendence. An explicit infinite set retains **exact degree d**
before the degree-at-most-d Koksma bridge is applied.

The normalized lower bound is divided in EReal with a positive finite degree.
`normalized_ge_degree` reuses `normalized_lower_ge`, whose existing proof
uses `normalized_lower_identity`; neither numerical budget is re-proved.
The proof chooses degrees beyond both a requested index and a real bound.
It also proves actual convergence to the top neighborhood filter, stronger
than the tail-unbounded/limsup assertion.

All 29 new certification declarations are listed in `scripts/Audit.lean`:

- `TNumbersLean.propositionB_eq`;
- `TNumbersLean.CriterionInputs.local_separation`;
- `TNumbersLean.CriterionInputs.source_error_factorization`;
- `TNumbersLean.CriterionInputs.source_error_ratio_bound`;
- `TNumbersLean.CriterionInputs.absorbed_local_bound`;
- `TNumbersLean.CriterionInputs.usableExponent_uniform_lower`;
- `TNumbersLean.CriterionInputs.eventually_admissible_heightRight_ge`;
- `TNumbersLean.CriterionInputs.transcendence`;
- `TNumbersLean.CriterionInputs.covered_scale_factor`;
- `TNumbersLean.CriterionInputs.height_half_absorption`;
- `TNumbersLean.CriterionInputs.global_separation_uniform`;
- `TNumbersLean.CriterionInputs.global_separation`;
- `TNumbersLean.CriterionInputs.upper_wStar_bound`;
- `TNumbersLean.CriterionInputs.wStar_lt_top`;
- `TNumbersLean.CriterionInputs.denominator_tends_to_infinity`;
- `TNumbersLean.CriterionInputs.center_height_tends_to_infinity`;
- `TNumbersLean.CriterionInputs.recurrent_center_heights_unbounded`;
- `TNumbersLean.CriterionInputs.recurrent_centers_infinite`;
- `TNumbersLean.CriterionInputs.recurrent_source_bound`;
- `TNumbersLean.CriterionInputs.eventually_recurrent_strong_approximation`;
- `TNumbersLean.CriterionInputs.recurrent_exact_approximants_infinite`;
- `TNumbersLean.CriterionInputs.recurrent_approximants_infinite`;
- `TNumbersLean.CriterionInputs.lower_wStar_bound`;
- `TNumbersLean.CriterionInputs.normalized_lower_bound`;
- `TNumbersLean.CriterionInputs.normalized_ge_degree`;
- `TNumbersLean.CriterionInputs.normalized_tail_unbounded`;
- `TNumbersLean.CriterionInputs.normalized_tends_to_top`;
- `TNumbersLean.CriterionInputs.isTNumber`;
- `TNumbersLean.proposition_three_two`.

### 5. ConcreteSchedule.lean — concrete schedule

`ScheduleThresholds` contains only natural thresholds `T`, monotonicity on
`{d | 2 ≤ d}`, `T d ≥ 4` for those degrees, an integer `Q₁`, and `T 2 ≤ Q₁`.
Thresholds at degrees zero and one are unused and unrestricted. No assertion
of Lemma 3.1 is an input.

All definitions and theorems below are in `TNumbersLean.ScheduleThresholds`.
Lean stage `k` represents manuscript stage `k+1`. Lean pair `i` represents
manuscript pair `j=i+1`: `2*i` is paper stage `2j-1`, and `2*i+1` is paper
stage `2j`. Thus `concreteD i` represents paper `D_{i+1}`.

- `availableDegrees i q` is the finite set of degrees `2 ≤ d ≤ i+2` with
  `T d ≤ q`.
- `selectDegree i q` is its maximum, implemented using `Nat.findGreatest`.
- `v₂ j` is mathlib's `padicValNat 2 j`; all scheduled arguments are positive.
- `pairScale` is a natural recursion starting at `Q₁`. Its successor performs
  exactly the odd-stage power update and then the even-stage power update.
- `concreteD`, `concreteDegree`, `concreteExponent`, and `concreteQ` recover
  the stage data from this recursion.
- `concreteCriterionSchedule` casts the natural scales to reals and fills
  every field with a proved theorem.

| Manuscript | Concrete certification |
| --- | --- |
| (3.1), genuine finite maximum | `concrete_availableDegrees_nonempty`, `concreteD_spec`, `concreteD_maximal`, `concreteD_isGreatest` |
| (3.2), degree prescriptions | `concreteDegree_even`, `concreteDegree_odd`; `concreteExponent` is definitionally the existing cubic exponent |
| (3.3), no additional scale jump | `concreteQ_even`, `concreteQ_odd`, `concreteQ_recurrence` |
| (3.4), delayed degree divergence | `eventually_concreteD_ge`, `concreteD_tends_to_infinity` |
| (3.4), recurrence of each degree | `v₂_witness`, `v₂_fiber_infinite`, `concrete_recurrent` |
| (3.5), threshold at both stages | `concrete_threshold` |
| (3.5), exponent bounds | `concreteExponent_bounds`: `27 ≤ A(k) ≤ (k+4)^3` |
| (3.5), lower scale growth | `concreteQ_growth`: `Q₁^(2^k) ≤ Q(k)` |
| Lemma 3.1, strict growth and divergence | `concreteQ_strictMono`, `concreteQ_tends_to_infinity`, `concreteQ_real_tends_to_infinity` |
| Lemma 3.1, admissibility within two stages | `eventual_odd_admissible`, `concrete_eventual_next_admissible` |
| (3.6), eventual consecutive scale gap | `concrete_eventual_scale_gap`, reusing the proved abstract numerical argument after constructing the instance |

The valuation witnesses are `j=2^r*(2*m+1)`. Their injective family gives an
infinite valuation fiber; removing the finite initial segment where `D<d`
leaves an infinite tail. Its injective image `j ↦ 2*j-1` consists of Lean
indices of the manuscript's even stages and has degree exactly `d`.

The even-stage threshold proof uses `d_even ≤ D`, monotonicity of `T` on
its actual domain, and the first power update. No threshold is used to
increase a scale directly. `D` tends to infinity by maximality once both the
pair index and its recursively generated scale exceed the fixed requirements.
No `CriterionSchedule` field is used to establish the construction properties;
only the final (3.6) corollary uses the completed instance. `lemma_three_one`
collects the concrete schedule properties and the one/two-stage scale gap
in a single manuscript-correspondence theorem.

## Adversarial audit of the concrete schedule

- `concreteD_isGreatest` identifies the selected degree with the actual
  greatest member of the finite set. `concrete_availableDegrees_nonempty`
  establishes nonemptiness at every pair from `T 2 ≤ Q₁ ≤ pairScale i`.
  The initial-scale lower bound uses positivity of the cubic exponent at
  every natural degree, so it does not presuppose nonemptiness or `D ≥ 2`.
- The pair recursion contains exactly two power updates. Thresholds enter
  only the bounded degree selection; no maximum or threshold replacement
  changes any scale.
- Degree recurrence removes a finite prefix from an infinite positive
  valuation fiber, then uses an injective map to stage indices. Every member
  of that image has the specified exact degree.
- Lean stages `2*i` and `2*i+1` are paper stages `2j-1` and `2j`, with
  `j=i+1`. The valuation argument is `i+1`, never zero. The cap `i+2` is
  paper `j+1`; the exponent bound `k+4` is paper stage number plus three;
  the growth exponent `2^k` is paper `2^(stage-1)`.
- The threshold proof splits both stage parities. At the second stage it
  uses the first update and `T(min D (2+v₂ j)) ≤ T D`.
- Every sufficiently late paper odd stage has degree above the target;
  one of the next two Lean indices is such a stage. This proves the gap
  field without assuming any schedule conclusion.
- The concrete instance is defined after all its component proofs. Only
  the final scale-gap corollary uses the existing abstract schedule theorem.
  `CriterionSchedule` and `CriterionInputs` have no added fields.

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
- In the height-coverage run, no manuscript file was modified and
  `PropositionThreeTwo.lean` had not yet been created.

## Adversarial statement audit of height coverage

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

## Validation of the complete conditional proposition

- `lake build`: passed (7361 jobs).
- `bash scripts/check.sh`: passed, including every project source and the
  full axiom audit with `warningAsError=true`.
- `grep -RInE '\b(sorry|admit)\b|^[[:space:]]*axiom\b' TNumbersLean scripts`:
  no output (exit status 1, meaning no matches).
- `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`
  for all 29 new theorems, including all principal local, global, exponent,
  infinitude, divergence, and final proposition declarations.
- `CriterionSchedule`, `CriterionInputs`, and `AlgebraicApproximationSystem`
  were not changed. No conclusion of the proposition became an input field.
- The manuscript `.tex` and `.pdf` were not modified.

## Validation of the concrete schedule

- `lake build`: passed (7362 jobs).
- `scripts/check.sh`: passed with shell tracing enabled; all ten source
  modules and the full axiom audit passed with `warningAsError=true`.
- The required project placeholder/custom-axiom search produced no output
  (exit status 1, meaning no matches).
- All 39 new theorems and all nine definitions, including the constructed
  instance, are listed in `scripts/Audit.lean` (48 new audit entries).
- Every new audit entry depends only on `propext`, `Classical.choice`, and
  `Quot.sound`. The principal maximum, degree-divergence, recurrence,
  threshold, scale-divergence, eventual-admissibility, instance, and
  `lemma_three_one` declarations report exactly these three axioms.
- The existing abstract interfaces and proposition proof were not changed.
  No naive-height or `CriterionInputs` implementation was added.
- The manuscript `.tex` and `.pdf` were not modified.

## Adversarial audit of Proposition 3.2

- Transcendence is proved from (3.14); no hypothesis states it.
- The reserve for usable exponents is uniform and strictly positive at
  admissible stages, so scale divergence genuinely controls every fixed height.
- The global separation proof covers every sufficiently large height, with
  H_n chosen before both the point-specific input object and beta.
- The sign of the negative scale exponent and positivity of its bases are
  proved explicitly; the power conversion and extra inverse-height loss
  give precisely H^(-B_n-1).
- Bounded-height exceptions appear only in the Northcott upper bridge.
- Recurrent index infinitude is converted to distinct center-value infinitude
  using diverging heights, without assuming injectivity of the center sequence.
- The exact-degree infinitude theorem preserves S.degree(alpha)=d.
- Both signs of w+1 are handled, and definition (1.1)'s strict inequalities
  are proved for every w<W_d.
- Upper Koksma finiteness and lower bounds are conclusions of proved bridges,
  never additional assumptions. The normalized limit is proved explicitly.
- Input fields were compared with Section 2 and Lemma 3.1; none contains a
  circular Proposition 3.2 conclusion, and none was added or strengthened.

## What remains for the concrete manuscript proposition

### A. Complete conditional proposition — verified

`proposition_three_two` takes only `I : CriterionInputs S s x` for the declared
algebraic system and schedule. It proves transcendence, the uniform global
height bound, both explicit Koksma exponent bounds, normalized tail
unboundedness, convergence to infinity, limsup top, and the T-number criterion.
All logical arguments of (3.12)--(3.20) are now kernel-checked from those inputs.

### B. Concrete proposition — verified from Section 2 inputs

The schedule obligation is complete: `ScheduleThresholds.concreteCriterionSchedule`
is constructed from the threshold data, and `concrete_threshold` proves the
threshold condition at every stage.

The actual system is `realAlgebraicApproximationSystem`, with all fields
proved. `concreteCriterionInputs` selects the reduced p_k/q_k witnesses from
membership in E(J;Q_1), constructs theta_{d_k}+p_k/q_k, and proves all input
fields. `concrete_proposition_three_two` now assembles the literal proposition.

Schmidt's theorem and Icen's height lemma remain external mathematical inputs
under the agreed scope. Their concrete Section 2 consequences are explicitly
packaged in `SectionTwoInputs`; no unconditional proof of these external
estimates is claimed. The existing proposition theorem can now be applied
directly to the concrete constructor.
Nonemptiness of E, Fourier measures, and digital properties belong to other
manuscript results and are not prerequisites for this conditional criterion.


## Actual real algebraic data

`ConcreteAlgebraicData.lean` implements `RealAlgebraicData.isAlg` as
`IsAlgebraic ℚ α`, and `degree` as `(minpoly ℚ α).natDegree`.
`degree_eq_finrank` identifies this with the degree of `ℚ(α)` over `ℚ`.

The pinned mathlib has denominator clearing, integer polynomial content,
primitive parts, Gauss's lemma, and finite polynomial root sets. It has no
naive-algebraic-height/Northcott module (the suggested `NumberTheory/Height`
directory is absent). The local construction uses
`IsLocalization.integerNormalization (nonZeroDivisors ℤ)` on `minpoly ℚ α`,
then divides by content via `Polynomial.primPart`. For algebraic α the result
is nonzero, primitive, irreducible over both ℤ and ℚ, vanishes at α, and has
exactly `degree α`. Its rational image is a nonzero scalar multiple of the
monic rational minimal polynomial.

`coefficientHeight` is the radius-one Gauss norm for the ordinary integer norm.
`coefficientHeight_eq_max` proves that it is literally the maximum absolute
integer coefficient. `naiveHeight` applies it to `primitiveMinpoly`.
`primitiveMinpoly_unique_sign` proves uniqueness up to sign among primitive
integer polynomials irreducible over ℚ with root α;
`naiveHeight_eq_of_primitive_minimal` proves height agreement for either sign.
Nonalgebraic default values are unused by the system's mathematical fields.

`northcott` counts polynomials through their first n+1 bounded integer
coefficients, then takes a finite union of real root sets of nonzero
polynomials. It proves finiteness of real values for every natural degree bound
and every real height bound, without an external Northcott hypothesis.
Rational translation of algebraicity and degree is also proved; no translated
height estimate, Icen theorem, or Schmidt theorem is proved here.

The constructor has no external mathematical parameters. No `CriterionInputs`
constructor or selection of E witnesses/centers is included in this module.


### Actual algebraic data validation

- `lake build` passed (7363 jobs).
- `bash scripts/check.sh` passed, run with shell tracing; all eleven source
  modules and `scripts/Audit.lean` passed with warnings treated as errors.
- The required placeholder/custom-axiom search returned no matches.
- All 37 new definitions and theorems are listed in `scripts/Audit.lean`.
- Every new declaration uses only `propext`, `Classical.choice`, and
  `Quot.sound` (or a subset). The principal degree positivity, height
  positivity, primitive polynomial identification, Northcott, and system
  constructor declarations each report exactly these three axioms.
- The abstract interfaces, existing proposition and concrete schedule were
  unchanged. The manuscript was not modified.


## Concrete E witnesses and CriterionInputs

`ConcreteCriterionInputs.lean` defines `theta d = (2 : ℝ) ^ (d : ℝ)⁻¹`.
`theta_polynomial_irreducible` proves integer irreducibility of `X^d - 2`
by Eisenstein at 2. Gauss's lemma and the root identity identify the rational
minimal polynomial; `theta_degree` proves actual degree d for d≥2.
Rational translation preserves both actual algebraicity and exact degree.

`MemE t J x` is literally `x ∈ J` and, for each Lean stage k, existence of
an integer p and natural q with q>0, `Nat.Coprime p.natAbs q`,
`concreteQ k ≤ q < 2*concreteQ k`, and
`|x - theta (concreteDegree k) - p/q| ≤ (1/4)*q^(-concreteExponent k)`.
Nat.Coprime states gcd(|p|,q)=1. Lean k is manuscript stage k+1.
For the manuscript J is its fixed bounded open interval. The predicate also
makes sense for any set J; the constructor needs only `J ⊆ (-R,R)` and R≥2.
This generality does not alter the membership conditions.

The `MemE.numerator` and `MemE.denominator` functions use Classical.choose
only on `memE_stage_witness`. `witness_spec`, `reduced`, `denominator_block`,
and `source_approximation` certify the selected reduced fractions.
`MemE.center k` is `theta (concreteDegree k) + (MemE.rational k : ℝ)`.
Its algebraicity and exact degree are proved. The source bound implies error
at most one, hence center membership in [-R-1,R+1] and |p/q|≤R+3.

`SectionTwoInputs t R` contains exactly:

- constants C_{d,R}≥1 and (2.2) for reduced p/q with |p/q|≤R+3;
- Lemma 2.1 for all 2≤d≤D, 1≤n<d, Q≥T_D, Q≤q<2Q, and centers in
  [-R-1,R+1], using the actual naive height. Separation requires no reducedness.

No degree, source approximation, interval membership, transcendence, global
lower bound, Koksma conclusion, or coverage conclusion is supplied by this
external structure. Schmidt's theorem and Icen's lemma are not formalized.

`concreteCriterionInputs` proves all `CriterionInputs` fields for
`realAlgebraicApproximationSystem` and `t.concreteCriterionSchedule`.
Only center-height comparison and local separation use `SectionTwoInputs`.
The separation proof explicitly uses `concrete_threshold` with D=d_k.
The schedule and actual algebraic system are not redefined or strengthened.

`concrete_proposition_three_two` applies `proposition_three_two` to this
constructor, retaining the explicit Section 2 premise. No proof of those
external estimates is claimed.


### Concrete CriterionInputs validation

- `lake build` passed (7364 jobs).
- `bash scripts/check.sh` passed, run with shell tracing. All twelve source
  modules and the audit passed with warnings treated as errors.
- The required project placeholder/custom-axiom search returned no matches.
- All 29 new audit entries are present. Every new declaration uses only
  `propext`, `Classical.choice`, and `Quot.sound` (or a subset). Theta
  algebraicity, theta exact degree, witness extraction, center algebraicity,
  center exact degree, and `concreteCriterionInputs` each report exactly
  these three axioms.
- The README correspondence table has three columns in every row, with
  separate concrete schedule and actual algebraic-data rows; no README
  expansion was made.
- The existing schedule, actual algebraic system, interfaces, and abstract
  proposition proof were unchanged. The manuscript was not modified.
- At the concrete-input commit `defb510`, no literal final Proposition 3.2
  wrapper had yet been created.


## Final concrete Proposition 3.2

Final theorem: `TNumbersLean.concrete_proposition_three_two` in
`ConcretePropositionThreeTwo.lean`.
Final verified commit: `FINAL_VERIFIED_COMMIT` (placeholder for the commit
named `Complete concrete verification of Proposition 3.2`; hash reported
when the commit is made).

The statement uses actual `IsAlgebraic ℚ`, `RealAlgebraicData.degree`, and
`RealAlgebraicData.naiveHeight`. Its Koksma exponents and IsTNumber predicate
use `realAlgebraicApproximationSystem`, so the exponent definition (1.1)
and criterion (1.2) now literally use the manuscript degree and naive height.
`propositionB` is precisely (3.9); `recurrentW` is precisely the lower bound
in (3.11). The concrete schedule and MemE are unchanged.

The eight conclusions are transcendence, the uniform global exclusion,
upper and lower Koksma bounds, normalized tail unboundedness, convergence
to top, limsup top, and the concrete T-number conclusion. For (3.10), the
height threshold is chosen before **both** y∈E and β. This stronger uniform
conclusion is assembled from the existing `global_separation_uniform` theorem;
all other conclusions come directly from `proposition_three_two` applied
to `concreteCriterionInputs`. No Diophantine proof is repeated.

`concrete_transcendence`, `concrete_global_separation`, `concrete_upper_wStar`,
`concrete_lower_wStar`, and `concrete_isTNumber` are projections of the final
theorem, not independent mathematical proofs.

The exact external premises are R≥2, the interval bound, threshold data and
initial scale in `ScheduleThresholds`, E-membership, and `SectionTwoInputs`.
The only unformalized mathematical results are (2.2) and Lemma 2.1 as packaged
in `SectionTwoInputs`. Neither E-membership nor either structure contains
transcendence, global exclusion, exponent bounds, or a T-number conclusion.
Schmidt's theorem and Icen's lemma themselves are not reproved in Lean.
There is no remaining concrete instantiation or wrapper obligation within
this agreed scope. The manuscript was not modified.


### Final validation

- `lake build` passed (7365 jobs).
- `bash scripts/check.sh` passed, run with shell tracing. All thirteen source
  modules and `scripts/Audit.lean` passed with warnings treated as errors.
- The required project placeholder/custom-axiom search returned no matches
  (empty output; grep exit status 1).
- All 205 audit entries use only standard allowed axioms. The final theorem
  and all five corollaries each report exactly `[propext, Classical.choice,
  Quot.sound]`.
- The README correspondence table has exactly three columns in every row;
  `git diff --check` passed.
- The manuscript was not modified; no merge to main was performed.
