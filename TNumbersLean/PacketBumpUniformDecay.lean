import TNumbersLean.PaperBumpFourierDecay

namespace TNumbersLean

/-- Uniform quadratic decay of the bump Fourier factor across a dyadic packet:
for `q < 2Q`, the worst decay scale is `(2Q)^A`. -/
theorem norm_packetFourier_paperBump_scaled_le
    {Q q A : ℕ} (hq : 0 < q) (hqhi : q < 2 * Q)
    (ell : ℤ) :
    ‖packetFourier paperBumpComplex
        ((ell : ℝ) / ((q : ℝ) ^ A))‖ ≤
      paperBumpFourierDecayConstant /
        (1 + |(ell : ℝ)| / (((2 * Q : ℕ) : ℝ) ^ A)) ^ 2 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hQ : 0 < Q := by omega
  have h2QR : (0 : ℝ) < ((2 * Q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 2) hQ)
  have hpow :
      (q : ℝ) ^ A ≤ (((2 * Q : ℕ) : ℝ) ^ A) := by
    gcongr
    exact_mod_cast hqhi.le
  have hratio :
      |(ell : ℝ)| / (((2 * Q : ℕ) : ℝ) ^ A) ≤
        |(ell : ℝ)| / ((q : ℝ) ^ A) :=
    div_le_div_of_nonneg_left (abs_nonneg _)
      (pow_pos hqR A) hpow
  have habs :
      |(ell : ℝ) / ((q : ℝ) ^ A)| =
        |(ell : ℝ)| / ((q : ℝ) ^ A) := by
    rw [abs_div, abs_of_pos (pow_pos hqR A)]
  have hden :
      (1 + |(ell : ℝ)| / (((2 * Q : ℕ) : ℝ) ^ A)) ^ 2 ≤
        (1 + |(ell : ℝ) / ((q : ℝ) ^ A)|) ^ 2 := by
    rw [habs]
    gcongr
  have hweighted :=
    paperBumpFourier_weighted_decay
      ((ell : ℝ) / ((q : ℝ) ^ A))
  have hmul :
      (1 + |(ell : ℝ)| / (((2 * Q : ℕ) : ℝ) ^ A)) ^ 2 *
          ‖packetFourier paperBumpComplex
            ((ell : ℝ) / ((q : ℝ) ^ A))‖ ≤
        paperBumpFourierDecayConstant := by
    exact (mul_le_mul_of_nonneg_right hden (norm_nonneg _)).trans hweighted
  have hdenpos :
      0 < (1 + |(ell : ℝ)| / (((2 * Q : ℕ) : ℝ) ^ A)) ^ 2 := by
    positivity
  apply (le_div_iff₀ hdenpos).2
  simpa [mul_comm] using hmul

end TNumbersLean
