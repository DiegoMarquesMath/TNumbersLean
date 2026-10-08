import Mathlib

namespace TNumbersLean

/-- The derivative-scale conversion used in Lemma 5.1. -/
theorem derivative_scale_identity :
    (5 : ℚ) / 100 = 1 / 20 := by
  norm_num

/-- The summable perturbation exponent. -/
theorem perturbation_exponent_identity :
    (1 : ℚ) / 20 - 1 / 4 = -(1 / 5) := by
  norm_num

/-- The derivative budget has ample room for A >= 27. -/
theorem derivative_budget (A : ℝ) (hA : 27 ≤ A) :
    3 * A + (1 : ℝ) / 20 ≤ 5 * A := by
  nlinarith

end TNumbersLean
