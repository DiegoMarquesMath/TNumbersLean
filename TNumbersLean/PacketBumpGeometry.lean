import TNumbersLean.PacketSupportSet
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace TNumbersLean

open Set

/-- One translated and rescaled bump occurring in the manuscript definition of
`g_{q,A,θ}`. -/
noncomputable def packetBumpTerm
    (φ : ℝ → ℝ) (q A : ℕ) (θ₀ : ℝ) (p : ℤ) (x : ℝ) : ℝ :=
  φ (((q : ℝ) ^ A) * (x - θ₀ - (p : ℝ) / (q : ℝ)))

/-- The support radius `q^{-A}/4` follows directly from the support
`(-1/4,1/4)` of the basic bump. -/
theorem packetBumpTerm_ne_zero_implies_approx
    {φ : ℝ → ℝ} (hφ : Function.support φ ⊆ Set.Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ))
    {q A : ℕ} (hq : 0 < q) {θ₀ : ℝ} {p : ℤ} {x : ℝ}
    (hx : packetBumpTerm φ q A θ₀ p x ≠ 0) :
    |x - θ₀ - (p : ℝ) / (q : ℝ)| <
      (1 / 4 : ℝ) * (q : ℝ) ^ (-(A : ℝ)) := by
  have hmem :
      ((q : ℝ) ^ A) * (x - θ₀ - (p : ℝ) / (q : ℝ)) ∈ Function.support φ := by
    simpa [packetBumpTerm, Function.mem_support] using hx
  have hIoo := hφ hmem
  have habs :
      |((q : ℝ) ^ A) * (x - θ₀ - (p : ℝ) / (q : ℝ))| < (1 / 4 : ℝ) := by
    rw [abs_lt]
    constructor
    · nlinarith [hIoo.1]
    · exact hIoo.2
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hscale : (0 : ℝ) < (q : ℝ) ^ A := pow_pos hqR A
  rw [abs_mul, abs_of_pos hscale] at habs
  have hdiv :
      |x - θ₀ - (p : ℝ) / (q : ℝ)| < (1 / 4 : ℝ) / ((q : ℝ) ^ A) := by
    rw [lt_div_iff₀ hscale]
    simpa [mul_comm] using habs
  calc
    |x - θ₀ - (p : ℝ) / (q : ℝ)|
        < (1 / 4 : ℝ) / ((q : ℝ) ^ A) := hdiv
    _ = (1 / 4 : ℝ) * (q : ℝ) ^ (-(A : ℝ)) := by
      rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hqR), Real.rpow_natCast]

end TNumbersLean
