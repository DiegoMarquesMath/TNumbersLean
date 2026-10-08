# Normality in Mahler's Class of T-Numbers

[![Lean verification](https://github.com/DiegoMarquesMath/TNumbersLean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/DiegoMarquesMath/TNumbersLean/actions/workflows/lean.yml)

Selective Lean 4 verification of the most sensitive exact calculations in Diego Marques's manuscript  
*Normality in Mahler's Class of T-Numbers*.

The project focuses on the arithmetic budgets that drive the common Diophantine criterion, the Fourier perturbation construction, and the controlled digit-block argument. It is intentionally **not** a complete formalization of the manuscript: external inputs such as Schmidt's theorem, the full measure-theoretic Fourier construction, and Weyl/Borel--Cantelli arguments remain outside the present scope.

## Verified components

### Proposition 3.2 — common Diophantine criterion

The file [`DiophantineBudget.lean`](TNumbersLean/DiophantineBudget.lean) formalizes the exact exponent calculations used to prove finite fixed-degree Koksma exponents together with divergent normalized lower bounds.

It includes:

- the cubic reserve
  [
  2(K_n+3)le (n+2)^3;
  ]
- the lower bound for the usable height exponent (u_{k,n});
- the overlap budget between consecutive admissible height ranges;
- the identity (K_n+1=(n+1)^2);
- the explicit exponent contributing to (B_n);
- the exact simplification
  [
  rac{(d+1)^3}{d^2}-rac1d
  = d+3+rac2d+rac1{d^2}.
  ]

Main Lean declarations:

- `TNumbersLean.cubic_gap`
- `TNumbersLean.usable_exponent_lower`
- `TNumbersLean.overlap_budget`
- `TNumbersLean.B_exponent_identity`
- `TNumbersLean.normalized_lower_identity`
- `TNumbersLean.normalized_lower_ge`

### Height-range overlap logic

[`HeightOverlap.lean`](TNumbersLean/HeightOverlap.lean) isolates the logical core of the last-admissible-stage argument: once the next left endpoint lies below the current right endpoint, every intermediate target height belongs to the current admissible range.

Lean declaration:

- `TNumbersLean.height_in_current_range`

### Fourier perturbation budget

[`FourierBudget.lean`](TNumbersLean/FourierBudget.lean) verifies the exact numerical identities behind the one-initial-scale perturbation argument in Lemma 5.1:

[
rac5{100}=rac1{20},
qquad
rac1{20}-rac14=-rac15,
]

together with the derivative budget
[
3A+rac1{20}le5A
qquad(Age27).
]

Main declarations:

- `TNumbersLean.derivative_scale_identity`
- `TNumbersLean.perturbation_exponent_identity`
- `TNumbersLean.derivative_budget`

### Digit-block construction

[`DigitBudget.lean`](TNumbersLean/DigitBudget.lean) checks the numerical constants and exponent losses in Sections 7--8:

[
2cdot 4^4=512,
qquad
16cdot512=8192,
]

[
4A+4le6A,
qquad
2A-4ge50 quad(Age27),
]

[
8192<2^{50},
qquad
100A-6A=94A.
]

Main declarations:

- `TNumbersLean.block_constant_512`
- `TNumbersLean.block_constant_8192`
- `TNumbersLean.digit_exponent_budget`
- `TNumbersLean.digit_power_exponent`
- `TNumbersLean.two_pow_fifty`
- `TNumbersLean.next_scale_exponent_identity`

## Correspondence with the manuscript

| Manuscript component | Lean source | Scope |
| --- | --- | --- |
| Proposition 3.2: cubic reserve and usable exponent | [DiophantineBudget.lean](TNumbersLean/DiophantineBudget.lean) | Verified calculation |
| Proposition 3.2: overlap of admissible height ranges | [DiophantineBudget.lean](TNumbersLean/DiophantineBudget.lean) | Verified exponent budget |
| Proposition 3.2: explicit (B_n)-exponent arithmetic | [DiophantineBudget.lean](TNumbersLean/DiophantineBudget.lean) | Verified calculation |
| Proposition 3.2: normalized lower-bound arithmetic | [DiophantineBudget.lean](TNumbersLean/DiophantineBudget.lean) | Verified calculation |
| Last-admissible-stage implication | [HeightOverlap.lean](TNumbersLean/HeightOverlap.lean) | Verified logical core |
| Lemma 5.1: Fourier perturbation exponent | [FourierBudget.lean](TNumbersLean/FourierBudget.lean) | Verified calculation |
| Sections 7--8: constants (512,8192) | [DigitBudget.lean](TNumbersLean/DigitBudget.lean) | Verified calculation |
| Section 8: exponent (94A_k) | [DigitBudget.lean](TNumbersLean/DigitBudget.lean) | Verified calculation |

## Proof architecture

| Component | Role in the manuscript |
| --- | --- |
| Diophantine reserve | Ensures the translated Schmidt lower bound dominates the source-approximation error. |
| Height-range overlap | Upgrades local separation at selected stages to control of all sufficiently large algebraic heights. |
| Recurrent exact degrees | Supplies the lower bounds forcing (w_d^*(x)/d	oinfty). |
| Fourier perturbation budget | Makes one initial scale sufficient for summable Fourier perturbations. |
| Digit-block budget | Keeps prescribed digital oscillation compatible with the fixed Diophantine recurrence. |

## Verification

The project is pinned to:

- Lean 4.24.0;
- mathlib v4.24.0.

To reproduce the verification:

```bash
lake exe cache get
bash scripts/check.sh
```

The verification script:

1. builds the complete project;
2. checks every project source with warnings treated as errors;
3. prints the axioms of all listed declarations;
4. fails if a listed theorem depends on `sorryAx`.

See [`VALIDATION.md`](VALIDATION.md) for the validation record.

## Scope

This is a **selective formalization**. It verifies exact algebraic, order-theoretic, and numerical calculations at the manuscript's most sensitive points.

It does **not** claim a machine-checked proof of:

- Schmidt's algebraic approximation theorem;
- the complete degree-schedule recursion as a theorem about sequences;
- the prime-number-theorem input;
- the construction and weak convergence of the Fourier measures;
- Borel--Cantelli, Weyl's criterion, or absolute normality;
- the full binary Cantor construction.

The purpose is narrower: to kernel-check the exact exponent budgets and logical overlap steps most vulnerable to sign, denominator, or arithmetic mistakes.

## Suggested manuscript wording

> A selective Lean 4 verification of the principal exponent calculations in the common Diophantine criterion, the Fourier perturbation budget, and the digit-block construction is available in the [TNumbersLean repository](https://github.com/DiegoMarquesMath/TNumbersLean).

Maintained by [Diego Marques](https://github.com/DiegoMarquesMath).
