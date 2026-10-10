import TNumbersLean.PacketConvolutionWeight

namespace TNumbersLean

open Complex
open scoped BigOperators

/-- Quadratic Fourier decay assumption for the test function in the packet
convolution step. -/
def HasQuadraticFourierBound (F : ℝ → ℂ) (D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ u : ℝ,
    ‖F u‖ ≤ D * (1 + |u|) ^ (-2 : ℝ)

/-- Weighted coefficient bound for a periodic packet Fourier series. -/
def HasWeightedPacketCoeffBound
    (G : ℤ → ℂ) (B s : ℝ) : Prop :=
  0 ≤ B ∧ ∀ ell : ℤ,
    (1 + |(ell : ℝ)|) ^ s * ‖G ell‖ ≤ B

/-- One term in the Fourier-series convolution. -/
noncomputable def packetConvolutionTerm
    (G : ℤ → ℂ) (F : ℝ → ℂ) (t : ℝ) (ell : ℤ) : ℂ :=
  G ell * F (t - (ell : ℝ))

/-- Remove the coefficient weight from a weighted coefficient bound. -/
theorem norm_le_of_weightedPacketCoeffBound
    {G : ℤ → ℂ} {B s : ℝ}
    (hG : HasWeightedPacketCoeffBound G B s)
    (ell : ℤ) :
    ‖G ell‖ ≤ B * (1 + |(ell : ℝ)|) ^ (-s) := by
  have hw : 0 < (1 + |(ell : ℝ)|) ^ s :=
    Real.rpow_pos_of_pos (by positivity) s
  have h := hG.2 ell
  have hdiv :
      ‖G ell‖ ≤ B / (1 + |(ell : ℝ)|) ^ s := by
    apply (le_div_iff₀ hw).2
    simpa [mul_comm] using h
  simpa [Real.rpow_neg (by positivity), div_eq_mul_inv] using hdiv

/-- Termwise weighted bound by the universal shifted kernel. -/
theorem weighted_norm_packetConvolutionTerm_le
    {G : ℤ → ℂ} {F : ℝ → ℂ} {B D s : ℝ}
    (hs0 : 0 ≤ s)
    (hG : HasWeightedPacketCoeffBound G B s)
    (hF : HasQuadraticFourierBound F D)
    (t : ℝ) (ell : ℤ) :
    (1 + |t|) ^ s *
        ‖packetConvolutionTerm G F t ell‖ ≤
      B * D * packetShiftedKernel s t ell := by
  have hGn :=
    norm_le_of_weightedPacketCoeffBound hG ell
  have hFn := hF.2 (t - (ell : ℝ))
  have hB : 0 ≤ B := hG.1
  have hD : 0 ≤ D := hF.1
  have hterm :
      ‖packetConvolutionTerm G F t ell‖ ≤
        (B * D) *
          ((1 + |(ell : ℝ)|) ^ (-s) *
            (1 + |t - (ell : ℝ)|) ^ (-2 : ℝ)) := by
    rw [packetConvolutionTerm, norm_mul]
    calc
      ‖G ell‖ * ‖F (t - (ell : ℝ))‖
          ≤ (B * (1 + |(ell : ℝ)|) ^ (-s)) *
              (D * (1 + |t - (ell : ℝ)|) ^ (-2 : ℝ)) := by
            exact mul_le_mul hGn hFn (norm_nonneg _) (by positivity)
      _ = (B * D) *
          ((1 + |(ell : ℝ)|) ^ (-s) *
            (1 + |t - (ell : ℝ)|) ^ (-2 : ℝ)) := by ring
  have htweight : 0 ≤ (1 + |t|) ^ s :=
    Real.rpow_nonneg (by positivity) s
  calc
    (1 + |t|) ^ s *
        ‖packetConvolutionTerm G F t ell‖
        ≤ (1 + |t|) ^ s *
            ((B * D) *
              ((1 + |(ell : ℝ)|) ^ (-s) *
                (1 + |t - (ell : ℝ)|) ^ (-2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hterm htweight
    _ = (B * D) *
        ((1 + |t|) ^ s *
          ((1 + |(ell : ℝ)|) ^ (-s) *
            (1 + |t - (ell : ℝ)|) ^ (-2 : ℝ))) := by ring
    _ ≤ (B * D) * packetShiftedKernel s t ell := by
      exact mul_le_mul_of_nonneg_left
        (weighted_convolution_factor_le hs0 t ell)
        (mul_nonneg hB hD)
    _ = B * D * packetShiftedKernel s t ell := rfl

/-- The convolution series is absolutely summable under the two decay
hypotheses. -/
theorem summable_packetConvolutionTerm
    {G : ℤ → ℂ} {F : ℝ → ℂ} {B D s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ (1 / 2 : ℝ))
    (hG : HasWeightedPacketCoeffBound G B s)
    (hF : HasQuadraticFourierBound F D)
    (t : ℝ) :
    Summable (packetConvolutionTerm G F t) := by
  have hweightOne : 1 ≤ (1 + |t|) ^ s :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) hs0
  have hBD : 0 ≤ B * D := mul_nonneg hG.1 hF.1
  have hk := summable_packetShiftedKernel hs0 hs t
  refine Summable.of_norm_bounded
    (hk.mul_left (B * D)) ?_
  intro ell
  have hw :=
    weighted_norm_packetConvolutionTerm_le hs0 hG hF t ell
  have hnorm :
      ‖packetConvolutionTerm G F t ell‖ ≤
        (1 + |t|) ^ s *
          ‖packetConvolutionTerm G F t ell‖ := by
    exact le_mul_of_one_le_left (norm_nonneg _) hweightOne
  exact hnorm.trans (by simpa [mul_assoc] using hw)

/-- Uniform weighted bound for the full convolution series. -/
theorem weighted_norm_tsum_packetConvolutionTerm_le
    {G : ℤ → ℂ} {F : ℝ → ℂ} {B D s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ (1 / 2 : ℝ))
    (hG : HasWeightedPacketCoeffBound G B s)
    (hF : HasQuadraticFourierBound F D)
    (t : ℝ) :
    (1 + |t|) ^ s *
        ‖∑' ell : ℤ, packetConvolutionTerm G F t ell‖ ≤
      B * D * packetConvolutionConstant := by
  have hsum := summable_packetConvolutionTerm hs0 hs hG hF t
  have hnormsum :=
    norm_tsum_le_tsum_norm hsum
  have htweight : 0 ≤ (1 + |t|) ^ s :=
    Real.rpow_nonneg (by positivity) s
  have hweightedSummable :
      Summable (fun ell : ℤ =>
        (1 + |t|) ^ s *
          ‖packetConvolutionTerm G F t ell‖) := by
    have hk := summable_packetShiftedKernel hs0 hs t
    refine Summable.of_nonneg_of_le
      (fun ell => mul_nonneg htweight (norm_nonneg _))
      (fun ell => weighted_norm_packetConvolutionTerm_le
        hs0 hG hF t ell)
      (hk.mul_left (B * D))
  calc
    (1 + |t|) ^ s *
        ‖∑' ell : ℤ, packetConvolutionTerm G F t ell‖
        ≤ (1 + |t|) ^ s *
            (∑' ell : ℤ, ‖packetConvolutionTerm G F t ell‖) :=
      mul_le_mul_of_nonneg_left hnormsum htweight
    _ = ∑' ell : ℤ,
          (1 + |t|) ^ s *
            ‖packetConvolutionTerm G F t ell‖ := by
      rw [tsum_mul_left]
    _ ≤ ∑' ell : ℤ,
          (B * D) * packetShiftedKernel s t ell := by
      exact hweightedSummable.tsum_le_tsum
        (fun ell => weighted_norm_packetConvolutionTerm_le
          hs0 hG hF t ell)
        ((summable_packetShiftedKernel hs0 hs t).mul_left (B * D))
    _ = (B * D) *
          (∑' ell : ℤ, packetShiftedKernel s t ell) := by
      rw [tsum_mul_left]
    _ ≤ (B * D) * packetConvolutionConstant := by
      exact mul_le_mul_of_nonneg_left
        (tsum_packetShiftedKernel_le hs0 hs t)
        (mul_nonneg hG.1 hF.1)
    _ = B * D * packetConvolutionConstant := rfl

end TNumbersLean
