# Validation record

## Environment

Lean 4.24.0 and mathlib v4.24.0, pinned by `lean-toolchain`, `lakefile.toml`,
and `lake-manifest.json`.

## Concrete Proposition 3.2

Final theorem: `TNumbersLean.concrete_proposition_three_two` in
[ConcretePropositionThreeTwo.lean](TNumbersLean/ConcretePropositionThreeTwo.lean).

Formal proof commit: [`45485edceb96ea46879e8f4ab174f3f1d953bbcc`](https://github.com/DiegoMarquesMath/TNumbersLean/tree/45485edceb96ea46879e8f4ab174f3f1d953bbcc)
(`Complete concrete verification of Proposition 3.2`).

The theorem assembles the certified concrete schedule (3.1)--(3.3), actual
rational algebraicity and degree, primitive integer minimal polynomial naive
height, elementary Northcott, and reduced witnesses/centers from `MemE`.
It gives transcendence, the global bound (3.10) with a threshold uniform in
both points of E and algebraic targets, both explicit Koksma bounds (3.11),
normalized tail unboundedness, convergence to top, limsup top, and IsTNumber.
The five named corollaries are projections of the concrete theorem.

## Exact external scope

Parameters are `t : ScheduleThresholds`, `J : Set ℝ`, R≥2,
`J ⊆ Set.Ioo (-R) R`, x, `MemE t J x`, and `SectionTwoInputs t R`.
For the manuscript J is its fixed bounded open interval; the theorem also
holds for any subset of (-R,R).

`ScheduleThresholds` contains the nondecreasing integer thresholds T_D≥4
and initial scale Q₁≥T₂. `SectionTwoInputs` supplies only the concrete
naive-height comparison (2.2) for reduced bounded rational translations,
including C_{d,R}≥1, and Lemma 2.1 translated-center separation at those
thresholds. No proposition conclusion is assumed.

Schmidt's theorem and Icen's lemma themselves are not reproved in Lean.
There are no remaining concrete-interface construction obligations for
Proposition 3.2 under this agreed external scope. Nonemptiness of E and the
Fourier/digit constructions are separate manuscript results.

## Final checks

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
- The manuscript was not modified in the formalization runs.

The audit is [scripts/Audit.lean](scripts/Audit.lean); the detailed record is
[docs/PROPOSITION_3_2.md](docs/PROPOSITION_3_2.md).
