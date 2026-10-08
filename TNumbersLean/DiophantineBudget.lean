import Mathlib

noncomputable section

namespace TNumbersLean

def K (n : ℝ) : ℝ := n * (n + 2)

def aCoeff (n : ℝ) : ℝ := 10000 * (n + 1)^3

def delta (n : ℝ) : ℝ :=
  1 / (40000 * (n + 1)^3 * (n + 2))

/-- The cubic reserve used in Proposition 3.2. -/
theorem cubic_gap (n : ℝ) (hn : 0 ≤ n) :
    2 * (K n + 3) ≤ (n + 2)^3 := by
  unfold K
  nlinarith [sq_nonneg n, mul_nonneg hn (sq_nonneg n)]

/-- The numerator defining the usable height exponent is at least A/2. -/
theorem usable_numerator_half (n A : ℝ)
    (hn : 0 ≤ n)
    (hA : (n + 2)^3 ≤ A) :
    A / 2 ≤ A - K n - 3 := by
  have hgap := cubic_gap n hn
  nlinarith

/-- Lower bound for the usable height exponent u_{k,n}. -/
theorem usable_exponent_lower (n A : ℝ)
    (hn : 0 ≤ n)
    (hA : (n + 2)^3 ≤ A) :
    A / (2 * (n + 2))
      ≤ (A - K n - 3) / (n + 2) := by
  have hden : 0 < n + 2 := by
    linarith
  have hnum := usable_numerator_half n A hn hA
  calc
    A / (2 * (n + 2)) = (A / 2) / (n + 2) := by
      rw [div_div]
    _ ≤ (A - K n - 3) / (n + 2) := by
      exact (div_le_div_iff_of_pos_right hden).2 hnum

/-- The identity K_n+1=(n+1)^2. -/
theorem K_add_one (n : ℝ) :
    K n + 1 = (n + 1)^2 := by
  unfold K
  ring

/-- The overlap exponent appearing in the next admissible scale. -/
theorem overlap_exponent_identity (n A : ℝ)
    (hn : 0 ≤ n) :
    aCoeff n * A * delta n = A / (4 * (n + 2)) := by
  have h1 : n + 1 ≠ 0 := by
    linarith
  have h2 : n + 2 ≠ 0 := by
    linarith
  unfold aCoeff delta
  field_simp [h1, h2]
  ring

/-- The next left endpoint lies below the current usable exponent. -/
theorem overlap_budget (n A : ℝ)
    (hn : 0 ≤ n)
    (hA : (n + 2)^3 ≤ A) :
    aCoeff n * A * delta n
      ≤ (A - K n - 3) / (n + 2) := by
  rw [overlap_exponent_identity n A hn]
  have hA0 : 0 ≤ A := by
    have hcube : 0 ≤ (n + 2)^3 := by
      positivity
    linarith
  have hden : 0 < n + 2 := by
    linarith
  have hquarter :
      A / (4 * (n + 2)) ≤ A / (2 * (n + 2)) := by
    calc
      A / (4 * (n + 2)) = (A / 4) / (n + 2) := by
        rw [div_div]
      _ ≤ (A / 2) / (n + 2) := by
        apply (div_le_div_iff_of_pos_right hden).2
        nlinarith
      _ = A / (2 * (n + 2)) := by
        rw [div_div]
  exact hquarter.trans (usable_exponent_lower n A hn hA)

/-- The explicit exponent appearing in B_n. -/
theorem B_exponent_identity (n : ℝ) (hn : 0 ≤ n) :
    (K n + 1) / delta n
      = 40000 * (n + 1)^5 * (n + 2) := by
  have h1 : n + 1 ≠ 0 := by
    linarith
  have h2 : n + 2 ≠ 0 := by
    linarith
  rw [K_add_one]
  unfold delta
  field_simp [h1, h2]

/-- Exact simplification of the normalized lower bound for w_d^*. -/
theorem normalized_lower_identity (d : ℝ) (hd : 0 < d) :
    (d + 1)^3 / d^2 - 1 / d
      = d + 3 + 2 / d + 1 / d^2 := by
  field_simp [ne_of_gt hd]
  ring

/-- The normalized lower bound dominates d. -/
theorem normalized_lower_ge (d : ℝ) (hd : 0 < d) :
    d ≤ (d + 1)^3 / d^2 - 1 / d := by
  rw [normalized_lower_identity d hd]
  have h1 : 0 ≤ 2 / d := by
    positivity
  have h2 : 0 ≤ 1 / d^2 := by
    positivity
  linarith

end TNumbersLean
