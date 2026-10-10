import TNumbersLean.PacketConvolutionKernel

namespace TNumbersLean

/-- Elementary multiplicative triangle inequality underlying the weighted
convolution argument. -/
theorem one_add_abs_le_mul_one_add_abs
    (t : ℝ) (ell : ℤ) :
    1 + |t| ≤
      (1 + |(ell : ℝ)|) * (1 + |t - (ell : ℝ)|) := by
  have ht :
      |t| ≤ |(ell : ℝ)| + |t - (ell : ℝ)| := by
    have hid :
        t = (ell : ℝ) + (t - (ell : ℝ)) := by ring
    calc
      |t| = |(ell : ℝ) + (t - (ell : ℝ))| := congrArg abs hid
      _ ≤ |(ell : ℝ)| + |t - (ell : ℝ)| :=
        abs_add_le (ell : ℝ) (t - (ell : ℝ))
  nlinarith [abs_nonneg (ell : ℝ), abs_nonneg (t - (ell : ℝ))]

/-- Weighted factorization used termwise in the Fourier-series convolution.
Multiplying by the target weight `(1+|t|)^s` converts the product of the
packet weight and quadratic test-function decay into the shifted kernel. -/
theorem weighted_convolution_factor_le
    {s : ℝ} (hs0 : 0 ≤ s) (t : ℝ) (ell : ℤ) :
    (1 + |t|) ^ s *
        ((1 + |(ell : ℝ)|) ^ (-s) *
          (1 + |t - (ell : ℝ)|) ^ (-2 : ℝ)) ≤
      packetShiftedKernel s t ell := by
  let A : ℝ := 1 + |t|
  let B : ℝ := 1 + |(ell : ℝ)|
  let C : ℝ := 1 + |t - (ell : ℝ)|
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hABC : A ≤ B * C := by
    simpa [A, B, C] using one_add_abs_le_mul_one_add_abs t ell
  have hpow : A ^ s ≤ (B * C) ^ s :=
    Real.rpow_le_rpow hA.le hABC hs0
  have hsplit : (B * C) ^ s = B ^ s * C ^ s := by
    rw [Real.mul_rpow hB.le hC.le]
  have hweight :
      0 ≤ B ^ (-s) * C ^ (-2 : ℝ) := by positivity
  have hmain :
      A ^ s * (B ^ (-s) * C ^ (-2 : ℝ)) ≤
        (B ^ s * C ^ s) *
          (B ^ (-s) * C ^ (-2 : ℝ)) := by
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_right hpow hweight
  have hsimp :
      (B ^ s * C ^ s) *
          (B ^ (-s) * C ^ (-2 : ℝ)) =
        C ^ (-(2 - s)) := by
    rw [mul_mul_mul_comm]
    rw [← Real.rpow_add hB, ← Real.rpow_add hC]
    simp only [add_neg_cancel, Real.rpow_zero, one_mul]
    congr 1
    ring
  simpa [A, B, C, packetShiftedKernel] using hmain.trans_eq hsimp

end TNumbersLean
