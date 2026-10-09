import TNumbersLean.PacketResidueAverageBound
import TNumbersLean.PacketBumpUniformDecay

namespace TNumbersLean

open Complex
open scoped BigOperators

theorem norm_primePacketCoeffFormula_eq_bump_mul_residue
    (q A : ℕ) (θ₀ : ℝ) (ell : ℤ) :
    ‖primePacketCoeffFormula q A θ₀ ell‖ =
      ‖packetFourier paperBumpComplex
          ((ell : ℝ) / ((q : ℝ) ^ A))‖ *
        ‖packetResidueFormula q ell‖ := by
  simpa [packetResidueFormula] using
    norm_primePacketCoeffFormula q A θ₀ ell

/-- Uniform bound for every single-prime contribution in one dyadic packet. -/
theorem norm_primePacketCoeffFormula_le_uniform
    {Q q A : ℕ} (hqmem : q ∈ packetPrimes Q)
    (θ₀ : ℝ) (ell : ℤ) :
    ‖primePacketCoeffFormula q A θ₀ ell‖ ≤
      (paperBumpFourierDecayConstant /
        (1 + |(ell : ℝ)| / (((2 * Q : ℕ) : ℝ) ^ A)) ^ 2) *
        ‖packetResidueFormula q ell‖ := by
  rw [norm_primePacketCoeffFormula_eq_bump_mul_residue]
  apply mul_le_mul_of_nonneg_right
  · exact norm_packetFourier_paperBump_scaled_le
      (mem_packetPrimes_iff.mp hqmem).2.2.pos
      (mem_packetPrimes_iff.mp hqmem).2.1 ell
  · exact norm_nonneg _

/-- Before using prime counting, the averaged coefficient is bounded by a
uniform bump-decay factor times an explicit arithmetic divisor envelope. -/
theorem norm_averagedPacketCoeffFormula_le_envelope
    {Q A : ℕ} (hQ : 2 ≤ Q) (θ₀ : ℝ) (ell : ℤ) :
    ‖averagedPacketCoeffFormula Q A θ₀ ell‖ ≤
      ‖(1 / ((packetPrimes Q).card : ℂ))‖ *
        (paperBumpFourierDecayConstant /
          (1 + |(ell : ℝ)| / (((2 * Q : ℕ) : ℝ) ^ A)) ^ 2) *
        (((packetPrimeDivisors Q ell.natAbs).card : ℝ) +
          ((packetPrimes Q).card : ℝ) / ((Q : ℝ) - 1)) := by
  let B : ℝ :=
    paperBumpFourierDecayConstant /
      (1 + |(ell : ℝ)| / (((2 * Q : ℕ) : ℝ) ^ A)) ^ 2
  have hB : 0 ≤ B := by
    unfold B
    exact div_nonneg paperBumpFourierDecayConstant_nonneg (sq_nonneg _)
  calc
    ‖averagedPacketCoeffFormula Q A θ₀ ell‖
        ≤ ‖(1 / ((packetPrimes Q).card : ℂ))‖ *
            ∑ q ∈ packetPrimes Q,
              ‖primePacketCoeffFormula q A θ₀ ell‖ :=
      norm_averagedPacketCoeffFormula_le Q A θ₀ ell
    _ ≤ ‖(1 / ((packetPrimes Q).card : ℂ))‖ *
          ∑ q ∈ packetPrimes Q,
            B * ‖packetResidueFormula q ell‖ := by
      gcongr
      apply Finset.sum_le_sum
      intro q hq
      exact norm_primePacketCoeffFormula_le_uniform hq θ₀ ell
    _ = ‖(1 / ((packetPrimes Q).card : ℂ))‖ *
          B *
          (∑ q ∈ packetPrimes Q,
            ‖packetResidueFormula q ell‖) := by
      rw [Finset.mul_sum]
      ring
    _ ≤ ‖(1 / ((packetPrimes Q).card : ℂ))‖ *
          B *
          (((packetPrimeDivisors Q ell.natAbs).card : ℝ) +
            ((packetPrimes Q).card : ℝ) / ((Q : ℝ) - 1)) := by
      gcongr
      exact sum_norm_packetResidueFormula_le hQ ell
    _ = _ := by
      rfl

end TNumbersLean
