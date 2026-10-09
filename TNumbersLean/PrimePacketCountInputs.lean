import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TNumbersLean.AveragedPacket

namespace TNumbersLean

/-- The sole prime-distribution input needed by the packet argument: a
Chebyshev/PNT-type lower bound for the number of primes in the dyadic window
`[Q,2Q)`.

The mathlib revision pinned by this project does not contain the prime number
theorem with a strong enough error-free corollary for dyadic windows, so this
standard analytic-number-theory fact is kept as an explicit interface. -/
structure PrimePacketCountInputs where
  constant : ℝ
  threshold : ℕ
  constant_pos : 0 < constant
  threshold_ge_two : 2 ≤ threshold
  lower :
    ∀ Q : ℕ, threshold ≤ Q →
      constant * (Q : ℝ) / Real.log (Q : ℝ) ≤
        ((packetPrimes Q).card : ℝ)

/-- Above the threshold, the packet prime set is nonempty. -/
theorem PrimePacketCountInputs.packetPrimes_nonempty
    (H : PrimePacketCountInputs) {Q : ℕ} (hQ : H.threshold ≤ Q) :
    (packetPrimes Q).Nonempty := by
  have hQtwo : 2 ≤ Q := H.threshold_ge_two.trans hQ
  have hQone : (1 : ℝ) < (Q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hQtwo)
  have hleft :
      0 < H.constant * (Q : ℝ) / Real.log (Q : ℝ) := by
    exact div_pos (mul_pos H.constant_pos (by positivity))
      (Real.log_pos hQone)
  have hcardR : (0 : ℝ) < ((packetPrimes Q).card : ℝ) :=
    hleft.trans_le (H.lower Q hQ)
  have hcard : 0 < (packetPrimes Q).card := by
    exact_mod_cast hcardR
  exact Finset.card_pos.mp hcard

/-- In particular, the normalization by the number of packet primes is
legitimate above the threshold. -/
theorem PrimePacketCountInputs.packetPrimes_card_ne_zero
    (H : PrimePacketCountInputs) {Q : ℕ} (hQ : H.threshold ≤ Q) :
    (packetPrimes Q).card ≠ 0 :=
  Finset.card_ne_zero.mpr (H.packetPrimes_nonempty hQ)

end TNumbersLean
