import Mathlib

namespace TNumbersLean

/-- Constant in the middle-half digit-block estimate. -/
theorem block_constant_512 :
    2 * 4^4 = (512 : ℕ) := by
  norm_num

/-- Constant appearing after substituting ell_k = Q_k^{-A_k}/2. -/
theorem block_constant_8192 :
    16 * 512 = (8192 : ℕ) := by
  norm_num

/-- The exponent weakening Q^{-4A-4} >= Q^{-6A}. -/
theorem digit_exponent_budget (A : ℕ) (hA : 2 ≤ A) :
    4 * A + 4 ≤ 6 * A := by
  omega

/-- At A >= 27 the exponent 2A-4 is at least 50. -/
theorem digit_power_exponent (A : ℕ) (hA : 27 ≤ A) :
    50 ≤ 2 * A - 4 := by
  omega

/-- The numerical inequality used to absorb the factor 8192. -/
theorem two_pow_fifty :
    (8192 : ℕ) < 2^50 := by
  norm_num

/-- The remaining exponent in Q_{k+1}|V|. -/
theorem next_scale_exponent_identity (A : ℝ) :
    100 * A - 6 * A = 94 * A := by
  ring

end TNumbersLean
