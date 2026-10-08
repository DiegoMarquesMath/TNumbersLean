# Proposition 3.2 formalization roadmap

This branch aims to formalize the complete logical proof of Proposition 3.2 of
*Normality in Mahler's Class of T-Numbers*, starting from the manuscript's
stated algebraic-approximation inputs.

## Scope boundary

The goal is to formalize Proposition 3.2 **from** the two inputs already isolated
in Section 2:

1. the translated-center separation supplied by Lemma 2.1;
2. the two-sided height comparison for the recurrent centers in (2.2).

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

### 1. KoksmaExponent.lean

Define the approximation predicate used in (1.1) and a paper-level w_n^*
based on infinitely many distinct real algebraic approximants.
Provide bridge lemmas from eventual lower bounds and from explicit infinite
families of good approximants.

### 2. CriterionInputs.lean

Package the Section 2 inputs needed by Proposition 3.2:

- algebraic-point predicate;
- degree and height functions;
- Northcott-type finiteness for bounded degree and height;
- local separation at admissible centers;
- degree/height comparison for recurrent exact-degree centers.

The concrete external theorems remain assumptions of this interface.

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
