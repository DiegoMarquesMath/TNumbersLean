# Proposition 3.2 formalization roadmap

This branch aims to formalize the complete logical proof of Proposition 3.2 of
*Normality in Mahler's Class of T-Numbers*, starting from the manuscript's
stated algebraic-approximation inputs.

**Completed on `prop3-full`: the complete logical proof of Proposition 3.2
from `CriterionSchedule` and `CriterionInputs`.** The concrete manuscript
schedule and the actual algebraic/naive-height data are not yet instantiated.

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
The literal connection from membership in the concrete E(J;Q_1) to those
interfaces remains pending.

## Modules

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

### B. Concrete instantiation — pending

Before identifying this theorem with the manuscript's literal Proposition 3.2:

1. Implement the concrete delayed schedule (3.1)--(3.3), with D_j, the
   valuation-based recurrent degrees, and natural scales, and prove all
   `CriterionSchedule` fields, including recurrence, divergence, and eventual
   admissibility. Prove the threshold condition Q_k>=T_{d_k} needed by Lemma 2.1.
2. Instantiate `AlgebraicApproximationSystem` with actual real algebraicity,
   actual degree, and primitive-minimal-polynomial naive height; supply the
   positivity and Northcott fields for those actual functions. Then the
   abstract `wStar` and `IsTNumber` literally use the manuscript's data.
3. From x belonging to the concrete E(J;Q_1), select the reduced p_k/q_k
   witnesses and construct centers theta_{d_k}+p_k/q_k. Prove the source and
   denominator fields, establish the bounded-translation/center conditions,
   and instantiate the exact-degree/height comparison (2.2) and separation
   Lemma 2.1 at the scheduled thresholds.

Schmidt's theorem and Icen's height lemma remain explicit external mathematical
inputs under the agreed scope. This run does not claim formal proofs of those
external results or a completed concrete interface instance. Once the concrete
constructors are supplied, the existing proposition theorem applies directly.
Nonemptiness of E, Fourier measures, and digital properties belong to other
manuscript results and are not prerequisites for this conditional criterion.
