# Validation record

## Environment

- Lean 4.24.0
- mathlib v4.24.0
- library: `TNumbersLean`

The environment is pinned by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

## Proposition 3.2

Proof commit:

[`05cb79aa572d156674c562ae0dd0120a5ae15a36`](https://github.com/DiegoMarquesMath/TNumbersLean/tree/05cb79aa572d156674c562ae0dd0120a5ae15a36)

The declaration

`TNumbersLean.proposition_three_two`

proves the complete logical content of Proposition 3.2 from the explicit
`CriterionSchedule` and `CriterionInputs` interfaces.

It includes:

- transcendence;
- the local separation estimate (3.12);
- absorption of the source error and (3.14);
- coverage of all sufficiently large heights via (3.16)--(3.18);
- the uniform global lower bound (3.10)/(3.19);
- the upper Koksma bound `wStar x n <= B_n`;
- infinitely many distinct recurrent exact-degree approximants;
- the lower Koksma bound in (3.11);
- normalized divergence (3.20), limsup `top`, and the T-number conclusion.

## Verification

Run:

```bash
lake exe cache get
bash scripts/check.sh
```

For the Proposition 3.2 proof commit:

- `lake build` passed with 7361 jobs;
- `scripts/check.sh` passed with warnings treated as errors;
- the project search for `sorry`, `admit`, and custom `axiom` declarations returned no matches;
- all 29 new audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The audit script is [`scripts/Audit.lean`](scripts/Audit.lean).

## Scope boundary

The completed theorem is currently conditional on two explicit interfaces.

`AlgebraicApproximationSystem` packages algebraicity, degree, naive-height behavior, and Northcott finiteness. `CriterionSchedule` and `CriterionInputs` package the schedule, selected centers, source approximation, height comparison, and the translated-center separation used from Section 2.

The remaining task is to instantiate these interfaces with the manuscript's concrete schedule (3.1)--(3.3), actual real algebraic degree and naive height, and the centers arising from membership in `E(J;Q_1)`.

Schmidt's theorem and Icen's height lemma remain external mathematical inputs rather than being reproved in Lean.

For the detailed theorem-by-theorem correspondence, see
[docs/PROP3_FORMALIZATION.md](docs/PROP3_FORMALIZATION.md).
