# Theorem 1.1 — formalization plan

This branch targets a full Lean 4 verification of Theorem 1.1 of
*Normality in Mahler's Class of T-Numbers*.

Theorem 1.1 asserts that every nonempty open interval contains:

1. a nonempty compact perfect set of absolutely normal T-numbers;
2. a nonempty compact perfect set of T-numbers that are simply normal in no integer base.

The Diophantine core is already complete on `main`: concrete Proposition 3.2,
the literal degree schedule, actual algebraic degree and primitive-minimal-polynomial
naive height, Northcott, E-witnesses, and the approximation centers are kernel-checked.

## External scope already fixed

The Section 2 height comparison (2.2) and translated-center separation
(Lemma 2.1) remain explicit external mathematical inputs. Schmidt's theorem
and Icen's lemma themselves are not reproved.

No additional conclusion of Theorem 1.1 may enter an input structure.

## Phase A — normality infrastructure

- define the paper-facing notion of normality/absolute normality;
- formalize the exponential sums used in the Weyl criterion;
- prove the square-moment estimate from Fourier decay;
- apply first Borel--Cantelli on the square subsequence;
- pass from squares to every N;
- intersect over all bases and nonzero frequencies;
- connect the resulting uniform distribution statement with normality;
- prove atomlessness from Fourier decay;
- formalize perfect-set extraction for atomless finite Borel measures.

## Phase B — Fourier construction / Theorem 1.2

- formalize the packet construction used in the paper;
- prove the perturbation and derivative bounds (some exact budgets are already checked);
- construct the limiting measure;
- prove compact support and inclusion in the concrete E(J;Q1);
- prove the stretched-logarithmic Fourier decay;
- invoke the verified Proposition 3.2 to certify every support point as a T-number;
- conclude the full statement of Theorem 1.2.

## Phase C — Theorem 1.1(i)

From Theorem 1.2 plus normality-from-Fourier-decay and perfect extraction,
construct a nonempty compact perfect set of absolutely normal T-numbers in
every nonempty open interval.

## Phase D — digital construction / Theorem 1.3

- formalize base-b zero frequency;
- formalize the digit-block lemma and its geometric interval loss;
- formalize the base/task schedule;
- construct the binary nested interval tree;
- prove compactness, nonemptiness, and perfectness;
- prove inclusion in E(J;Q1), hence T-number status via Proposition 3.2;
- prove the liminf <= 1/4 and limsup >= 3/4 oscillation simultaneously in every base;
- conclude the full statement of Theorem 1.3.

## Phase E — Theorem 1.1(ii) and final main theorem

- deduce failure of simple normality in every base from the zero-frequency oscillation;
- combine parts (i) and (ii) into one paper-facing theorem `theorem_one_one`;
- audit all assumptions, axioms, and theorem correspondence;
- update README/VALIDATION only after the final theorem is kernel-checked.

## Verification discipline

Every milestone is accepted only after GitHub Actions passes the repository's
`scripts/check.sh` workflow. The audit must reject `sorryAx`; no project-level
`sorry`, `admit`, or custom `axiom` declarations are permitted.

Standard imported mathematical theorems from mathlib are allowed. Any manuscript
input that is not formalized must be stated explicitly and must not encode a conclusion
of Theorem 1.1.
