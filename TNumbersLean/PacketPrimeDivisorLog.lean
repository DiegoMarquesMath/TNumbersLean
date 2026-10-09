import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TNumbersLean.PacketPrimeDivisorCount

namespace TNumbersLean

/-- Real-logarithmic form of the packet prime-divisor count. -/
theorem card_packetPrimeDivisors_le_log_div
    {Q n : ℕ} (hQ : 1 < Q) (hn : n ≠ 0) :
    ((packetPrimeDivisors Q n).card : ℝ) ≤
      Real.log (n : ℝ) / Real.log (Q : ℝ) := by
  have hpowNat :=
    pow_card_packetPrimeDivisors_le (Q := Q) (n := n) hn
  have hpow :
      (Q : ℝ) ^ (packetPrimeDivisors Q n).card ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans hQ)
  have hlogmul :=
    Real.le_log_of_pow_le hQpos hpow
  have hlogQ : 0 < Real.log (Q : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hQ)
  apply (le_div_iff₀ hlogQ).2
  simpa using hlogmul

/-- Padded form used in the manuscript, avoiding a special case at small
frequencies. -/
theorem card_packetPrimeDivisors_le_padded_log_div
    {Q n : ℕ} (hQ : 1 < Q) (hn : n ≠ 0) :
    ((packetPrimeDivisors Q n).card : ℝ) ≤
      Real.log (2 + (n : ℝ)) / Real.log (Q : ℝ) := by
  have hbase :=
    card_packetPrimeDivisors_le_log_div (Q := Q) (n := n) hQ hn
  have hlogQ : 0 < Real.log (Q : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hQ)
  refine hbase.trans ?_
  apply div_le_div_of_nonneg_right _ hlogQ.le
  rw [Real.log_le_log_iff]
  · linarith
  · exact_mod_cast Nat.pos_of_ne_zero hn
  · positivity

/-- Integer-frequency version of the manuscript divisor-count estimate. -/
theorem card_packetPrimeDivisors_natAbs_le_padded_log_div
    {Q : ℕ} (hQ : 1 < Q) {ell : ℤ} (hell : ell ≠ 0) :
    ((packetPrimeDivisors Q ell.natAbs).card : ℝ) ≤
      Real.log (2 + (ell.natAbs : ℝ)) / Real.log (Q : ℝ) := by
  exact card_packetPrimeDivisors_le_padded_log_div
    hQ (Int.natAbs_ne_zero.mpr hell)

end TNumbersLean
