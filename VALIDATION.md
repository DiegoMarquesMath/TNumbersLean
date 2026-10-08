# Validation record

## Initial selective formalization — 8 October 2026

This repository accompanies Diego Marques's manuscript  
*Normality in Mahler's Class of T-Numbers*.

The present development is intentionally selective. It formalizes exact calculations at the manuscript's most sensitive arithmetic points rather than the full analytic and measure-theoretic proof.

### Environment

- Lean: 4.24.0
- mathlib: v4.24.0
- project library: `TNumbersLean`

The dependency revisions are pinned by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

### Local build

A local macOS build completed successfully:

```text
Build completed successfully (7356 jobs).
```

This certifies that the project sources compile against the pinned Lean/mathlib environment. The stronger repository audit is performed by `scripts/check.sh` and by GitHub Actions.

### Audited declarations

The audit script lists the axioms of the following declarations.

#### Diophantine budget

- `TNumbersLean.cubic_gap`
- `TNumbersLean.usable_numerator_half`
- `TNumbersLean.usable_exponent_lower`
- `TNumbersLean.K_add_one`
- `TNumbersLean.overlap_exponent_identity`
- `TNumbersLean.overlap_budget`
- `TNumbersLean.B_exponent_identity`
- `TNumbersLean.normalized_lower_identity`
- `TNumbersLean.normalized_lower_ge`

#### Schedule budget

- `TNumbersLean.consecutive_admissible_gap_le_two`
- `TNumbersLean.skipped_stage_not_admissible`
- `TNumbersLean.skipped_degree_le`
- `TNumbersLean.stageExponent_le_of_degree_le`
- `TNumbersLean.skipped_stage_exponent_le`
- `TNumbersLean.two_step_schedule_exponent_le`
- `TNumbersLean.one_step_schedule_exponent_le`

#### Fourier budget

- `TNumbersLean.derivative_scale_identity`
- `TNumbersLean.perturbation_exponent_identity`
- `TNumbersLean.derivative_budget`

#### Digit budget

- `TNumbersLean.block_constant_512`
- `TNumbersLean.block_constant_8192`
- `TNumbersLean.digit_exponent_budget`
- `TNumbersLean.digit_power_exponent`
- `TNumbersLean.two_pow_fifty`
- `TNumbersLean.next_scale_exponent_identity`

#### Height overlap

- `TNumbersLean.height_in_current_range`

### Verification script

Run:

```bash
lake exe cache get
bash scripts/check.sh
```

The script:

1. runs `lake build`;
2. checks every `TNumbersLean/*.lean` file with `warningAsError=true`;
3. runs `scripts/Audit.lean`;
4. prints theorem axioms;
5. fails if the audit output contains `sorryAx`.

### Continuous integration

The repository includes a GitHub Actions workflow:

[`.github/workflows/lean.yml`](.github/workflows/lean.yml)

It runs on pushes, pull requests, and manual dispatch.

The status badge in the README reflects the current state of the main branch.

### Mathematical correspondence

The formalized statements correspond to calculations used in:

- Lemma 3.1 / equation (3.6): bounded gaps between admissible stages and the one- and two-step exponent budgets;\n- Proposition 3.2: cubic reserve, usable height exponent, overlap budget, and explicit (B_n)-exponent;
- Lemma 5.1: the one-initial-scale perturbation exponent;
- Sections 7--8: the constants (512), (8192), the weakening (4A+4le6A), the bound (2A-4ge50), and the exponent (94A);
- the last-admissible-stage logical implication covering intermediate heights.

### Scope limitation

Kernel verification applies only to the Lean statements listed above.

The repository does not currently formalize the external Schmidt theorem, the full concrete recursion defining $D_j$ and $d_k$ beyond the bounded-gap core, prime-counting estimates, weak convergence of measures, Weyl's criterion, or the complete Cantor constructions.

Accordingly, the repository should be cited as a **selective Lean verification**, not as a full formalization of Theorems 1.1--1.3.
