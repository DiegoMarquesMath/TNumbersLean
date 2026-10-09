import TNumbersLean.PacketPrimeDivisorLog
import TNumbersLean.PrimePacketCountInputs

namespace TNumbersLean

/-- The exceptional packet primes dividing a nonzero frequency occupy at most
a logarithmic proportion of the dyadic prime packet.  This is the exact
cancellation of the two factors log Q in the manuscript. -/
theorem packetPrimeDivisor_ratio_le
    (H : PrimePacketCountInputs)
    {Q : ℕ} (hQ : H.threshold ≤ Q)
    {ell : ℤ} (hell : ell ≠ 0) :
    ((packetPrimeDivisors Q ell.natAbs).card : ℝ) /
        ((packetPrimes Q).card : ℝ) ≤
      Real.log (2 + (ell.natAbs : ℝ)) /
        (H.constant * (Q : ℝ)) := by
  have hQtwo : 2 ≤ Q := H.threshold_ge_two.trans hQ
  have hQone : (1 : ℝ) < (Q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hQtwo)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos hQone
  have hlogN :
      0 < Real.log (2 + (ell.natAbs : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 2 + ell.natAbs by omega)
  have hcount :=
    card_packetPrimeDivisors_natAbs_le_padded_log_div
      (Q := Q) (lt_of_lt_of_le Nat.one_lt_two hQtwo) hell
  have hlower := H.lower Q hQ
  have hlowerpos :
      0 < H.constant * (Q : ℝ) / Real.log (Q : ℝ) :=
    div_pos (mul_pos H.constant_pos (by positivity)) hlogQ
  have hcardpos :
      0 < ((packetPrimes Q).card : ℝ) :=
    hlowerpos.trans_le hlower
  calc
    ((packetPrimeDivisors Q ell.natAbs).card : ℝ) /
          ((packetPrimes Q).card : ℝ)
        ≤ (Real.log (2 + (ell.natAbs : ℝ)) /
              Real.log (Q : ℝ)) /
            ((packetPrimes Q).card : ℝ) :=
      div_le_div_of_nonneg_right hcount hcardpos.le
    _ ≤ (Real.log (2 + (ell.natAbs : ℝ)) /
              Real.log (Q : ℝ)) /
            (H.constant * (Q : ℝ) / Real.log (Q : ℝ)) := by
      exact div_le_div_of_nonneg_left
        (div_nonneg hlogN.le hlogQ.le) hlowerpos hlower
    _ = Real.log (2 + (ell.natAbs : ℝ)) /
          (H.constant * (Q : ℝ)) := by
      field_simp [hlogQ.ne', H.constant_pos.ne']
      ring

/-- The complex normalization used in the averaged coefficient has the
expected real norm. -/
theorem norm_inv_packetPrimes_card
    {Q : ℕ} (hcard : (packetPrimes Q).card ≠ 0) :
    ‖(1 / ((packetPrimes Q).card : ℂ))‖ =
      1 / ((packetPrimes Q).card : ℝ) := by
  rw [norm_div, norm_one]
  congr 1
  simp

end TNumbersLean
