import TNumbersLean.PacketPrimeCountRatio

namespace TNumbersLean

/-- Elementary dyadic denominator estimate. -/
theorem one_div_Q_sub_one_le_two_div_Q
    {Q : ℕ} (hQ : 2 ≤ Q) :
    (1 : ℝ) / ((Q : ℝ) - 1) ≤ 2 / (Q : ℝ) := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := by positivity
  have hden : (0 : ℝ) < (Q : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hQ))
  rw [div_le_div_iff₀ hden hQpos]
  have hnat : Q ≤ 2 * (Q - 1) := by omega
  exact_mod_cast hnat

/-- For a nonzero integer frequency, the harmless 2/Q term is absorbed by
the same logarithmic factor as the exceptional-prime contribution. -/
theorem two_div_Q_le_log_term
    {Q : ℕ} (hQ : 0 < Q) {ell : ℤ} (hell : ell ≠ 0) :
    (2 : ℝ) / (Q : ℝ) ≤
      ((2 : ℝ) / Real.log 2) *
        Real.log (2 + (ell.natAbs : ℝ)) / (Q : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlog :
      Real.log (2 : ℝ) ≤
        Real.log (2 + (ell.natAbs : ℝ)) := by
    apply Real.log_le_log
    · norm_num
    · have hnpos : 0 < ell.natAbs :=
        Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hell)
      exact_mod_cast (show 2 ≤ 2 + ell.natAbs by omega)
  have hnum :
      (2 : ℝ) ≤
        ((2 : ℝ) / Real.log 2) *
          Real.log (2 + (ell.natAbs : ℝ)) := by
    calc
      (2 : ℝ) =
          ((2 : ℝ) / Real.log 2) * Real.log 2 := by
            field_simp [hlog2.ne']
      _ ≤ ((2 : ℝ) / Real.log 2) *
          Real.log (2 + (ell.natAbs : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hlog
              (div_nonneg (by norm_num) hlog2.le)
  exact div_le_div_of_nonneg_right hnum (by positivity)

/-- Explicit arithmetic constant in the averaged packet coefficient bound. -/
noncomputable def packetCoefficientArithmeticConstant
    (H : PrimePacketCountInputs) : ℝ :=
  1 / H.constant + 2 / Real.log 2

theorem packetCoefficientArithmeticConstant_pos
    (H : PrimePacketCountInputs) :
    0 < packetCoefficientArithmeticConstant H := by
  unfold packetCoefficientArithmeticConstant
  have hlog2 : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  exact add_pos (one_div_pos.mpr H.constant_pos)
    (div_pos (by norm_num) hlog2)

/-- The normalized arithmetic envelope has exactly the logarithmic shape used
in the manuscript. -/
theorem normalized_packet_arithmetic_envelope_le
    (H : PrimePacketCountInputs)
    {Q : ℕ} (hQ : H.threshold ≤ Q)
    {ell : ℤ} (hell : ell ≠ 0) :
    ((packetPrimeDivisors Q ell.natAbs).card : ℝ) /
        ((packetPrimes Q).card : ℝ) +
      1 / ((Q : ℝ) - 1) ≤
      packetCoefficientArithmeticConstant H *
        Real.log (2 + (ell.natAbs : ℝ)) / (Q : ℝ) := by
  have hQtwo : 2 ≤ Q := H.threshold_ge_two.trans hQ
  have hratio := packetPrimeDivisor_ratio_le H hQ hell
  have hgeneric :=
    one_div_Q_sub_one_le_two_div_Q hQtwo
  have hlogterm :=
    two_div_Q_le_log_term
      (lt_of_lt_of_le (by decide : 0 < 2) hQtwo) hell
  calc
    ((packetPrimeDivisors Q ell.natAbs).card : ℝ) /
          ((packetPrimes Q).card : ℝ) +
        1 / ((Q : ℝ) - 1)
        ≤ Real.log (2 + (ell.natAbs : ℝ)) /
              (H.constant * (Q : ℝ)) +
            1 / ((Q : ℝ) - 1) :=
      add_le_add hratio le_rfl
    _ ≤ Real.log (2 + (ell.natAbs : ℝ)) /
              (H.constant * (Q : ℝ)) +
            2 / (Q : ℝ) :=
      add_le_add_left hgeneric _
    _ ≤ Real.log (2 + (ell.natAbs : ℝ)) /
              (H.constant * (Q : ℝ)) +
            ((2 : ℝ) / Real.log 2) *
              Real.log (2 + (ell.natAbs : ℝ)) / (Q : ℝ) :=
      add_le_add_left hlogterm _
    _ = packetCoefficientArithmeticConstant H *
          Real.log (2 + (ell.natAbs : ℝ)) / (Q : ℝ) := by
      unfold packetCoefficientArithmeticConstant
      have hc : H.constant ≠ 0 := H.constant_pos.ne'
      have hQne : (Q : ℝ) ≠ 0 := by positivity
      field_simp [hc, hQne]

end TNumbersLean
