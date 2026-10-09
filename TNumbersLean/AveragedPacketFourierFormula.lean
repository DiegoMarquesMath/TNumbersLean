import TNumbersLean.PeriodizedPrimePacketFourier
import TNumbersLean.PaperBumpFourierDecay
import TNumbersLean.PacketPrimeDivisorLog
import TNumbersLean.PrimePacketCountInputs

namespace TNumbersLean

open Complex
open scoped BigOperators FourierTransform

/-- The closed formula for the Fourier coefficient of one prime packet,
defined without any typeclass dependence on the denominator. -/
noncomputable def primePacketCoeffFormula
    (q A : ℕ) (θ₀ : ℝ) (ell : ℤ) : ℂ :=
  (Real.fourierChar (-θ₀ * (ell : ℝ)) : ℂ) *
    packetFourier paperBumpComplex
      ((ell : ℝ) / ((q : ℝ) ^ A)) *
    (((q : ℂ) / ((q : ℂ) - 1)) *
        (if q ∣ ell.natAbs then 1 else 0) -
      1 / ((q : ℂ) - 1))

/-- For a prime denominator, the formula agrees with the coefficient already
obtained from the periodized single-prime packet. -/
theorem primePacketCoeffFormula_eq_periodized
    {q A : ℕ} [NeZero q] (hq : Nat.Prime q)
    (θ₀ : ℝ) (ell : ℤ) :
    primePacketCoeffFormula q A θ₀ ell =
      periodizedPrimePacketCoeff (A := A) hq θ₀ ell := by
  exact (periodizedPrimePacketCoeff_eq_manuscript
    (A := A) hq θ₀ ell).symm

/-- Formula-side Fourier coefficient of the averaged packet.  The definition
uses the closed single-prime formula, so no denominator-dependent typeclass
instances occur inside the finite sum. -/
noncomputable def averagedPacketCoeffFormula
    (Q A : ℕ) (θ₀ : ℝ) (ell : ℤ) : ℂ :=
  (1 / ((packetPrimes Q).card : ℂ)) *
    ∑ q ∈ packetPrimes Q, primePacketCoeffFormula q A θ₀ ell

/-- Elementary triangle inequality for the averaged packet coefficient. -/
theorem norm_averagedPacketCoeffFormula_le
    (Q A : ℕ) (θ₀ : ℝ) (ell : ℤ) :
    ‖averagedPacketCoeffFormula Q A θ₀ ell‖ ≤
      ‖(1 / ((packetPrimes Q).card : ℂ))‖ *
        ∑ q ∈ packetPrimes Q,
          ‖primePacketCoeffFormula q A θ₀ ell‖ := by
  rw [averagedPacketCoeffFormula, norm_mul]
  gcongr
  exact norm_sum_le _ _

/-- The common translation phase in every prime coefficient has norm one. -/
theorem norm_primePacketCoeffFormula
    (q A : ℕ) (θ₀ : ℝ) (ell : ℤ) :
    ‖primePacketCoeffFormula q A θ₀ ell‖ =
      ‖packetFourier paperBumpComplex
          ((ell : ℝ) / ((q : ℝ) ^ A))‖ *
        ‖(((q : ℂ) / ((q : ℂ) - 1)) *
            (if q ∣ ell.natAbs then 1 else 0) -
          1 / ((q : ℂ) - 1))‖ := by
  rw [primePacketCoeffFormula, norm_mul, norm_mul]
  simp

end TNumbersLean
