import TNumbersLean.AveragedPacketCoefficientEnvelope
import TNumbersLean.PacketArithmeticEnvelope

namespace TNumbersLean

/-- Constant in the averaged packet Fourier-coefficient estimate. -/
noncomputable def averagedPacketFourierConstant
    (H : PrimePacketCountInputs) : ℝ :=
  paperBumpFourierDecayConstant *
    packetCoefficientArithmeticConstant H

theorem averagedPacketFourierConstant_nonneg
    (H : PrimePacketCountInputs) :
    0 ≤ averagedPacketFourierConstant H := by
  unfold averagedPacketFourierConstant
  exact mul_nonneg paperBumpFourierDecayConstant_nonneg
    (packetCoefficientArithmeticConstant_pos H).le

/-- The quantitative Fourier-coefficient estimate for the averaged packet.
This is the coefficient bound used in the manuscript before the weighted
elementary estimate. -/
theorem norm_averagedPacketCoeffFormula_le_logarithmic
    (H : PrimePacketCountInputs)
    {Q A : ℕ} (hQ : H.threshold ≤ Q)
    (θ₀ : ℝ) {ell : ℤ} (hell : ell ≠ 0) :
    ‖averagedPacketCoeffFormula Q A θ₀ ell‖ ≤
      averagedPacketFourierConstant H *
        Real.log (2 + (ell.natAbs : ℝ)) / (Q : ℝ) /
        (1 + |(ell : ℝ)| / (((2 * Q : ℕ) : ℝ) ^ A)) ^ 2 := by
  have hQtwo : 2 ≤ Q := H.threshold_ge_two.trans hQ
  have henv :=
    norm_averagedPacketCoeffFormula_le_envelope
      (A := A) hQtwo θ₀ ell
  rw [norm_inv_packetPrimes_card Q] at henv
  let B : ℝ :=
    paperBumpFourierDecayConstant /
      (1 + |(ell : ℝ)| / (((2 * Q : ℕ) : ℝ) ^ A)) ^ 2
  have hB : 0 ≤ B := by
    unfold B
    exact div_nonneg paperBumpFourierDecayConstant_nonneg (sq_nonneg _)
  have hcardNat := H.packetPrimes_card_ne_zero hQ
  have hcardR : ((packetPrimes Q).card : ℝ) ≠ 0 := by
    exact_mod_cast hcardNat
  have hQsub :
      (Q : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (Q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hQtwo)
    exact (sub_pos.mpr this).ne'
  have harith :=
    normalized_packet_arithmetic_envelope_le H hQ hell
  have hnormalize :
      (1 / ((packetPrimes Q).card : ℝ)) * B *
          (((packetPrimeDivisors Q ell.natAbs).card : ℝ) +
            ((packetPrimes Q).card : ℝ) / ((Q : ℝ) - 1)) =
        B *
          (((packetPrimeDivisors Q ell.natAbs).card : ℝ) /
              ((packetPrimes Q).card : ℝ) +
            1 / ((Q : ℝ) - 1)) := by
    field_simp [hcardR, hQsub]
  calc
    ‖averagedPacketCoeffFormula Q A θ₀ ell‖
        ≤ (1 / ((packetPrimes Q).card : ℝ)) * B *
          (((packetPrimeDivisors Q ell.natAbs).card : ℝ) +
            ((packetPrimes Q).card : ℝ) / ((Q : ℝ) - 1)) := by
      simpa [B] using henv
    _ = B *
          (((packetPrimeDivisors Q ell.natAbs).card : ℝ) /
              ((packetPrimes Q).card : ℝ) +
            1 / ((Q : ℝ) - 1)) :=
      hnormalize
    _ ≤ B *
          (packetCoefficientArithmeticConstant H *
            Real.log (2 + (ell.natAbs : ℝ)) / (Q : ℝ)) :=
      mul_le_mul_of_nonneg_left harith hB
    _ = averagedPacketFourierConstant H *
        Real.log (2 + (ell.natAbs : ℝ)) / (Q : ℝ) /
        (1 + |(ell : ℝ)| / (((2 * Q : ℕ) : ℝ) ^ A)) ^ 2 := by
      unfold B averagedPacketFourierConstant
      ring

end TNumbersLean
