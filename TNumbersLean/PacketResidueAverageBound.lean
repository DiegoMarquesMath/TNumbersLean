import TNumbersLean.AveragedPacketFourierFormula

namespace TNumbersLean

open Complex
open scoped BigOperators

/-- The residual arithmetic factor in the single-prime packet coefficient. -/
noncomputable def packetResidueFormula (q : ℕ) (ell : ℤ) : ℂ :=
  ((q : ℂ) / ((q : ℂ) - 1)) *
      (if q ∣ ell.natAbs then 1 else 0) -
    1 / ((q : ℂ) - 1)

/-- For a prime denominator, the closed residue formula agrees with the
abstract residue factor from the finite character sum. -/
theorem packetResidueFormula_eq_factor
    {q : ℕ} [NeZero q] (hq : Nat.Prime q) (ell : ℤ) :
    packetResidueFormula q ell = packetResidueFactor q ell := by
  exact (packetResidueFactor_eq_manuscript hq ell).symm

theorem norm_packetResidueFormula_of_dvd
    {q : ℕ} [NeZero q] (hq : Nat.Prime q) {ell : ℤ}
    (hd : q ∣ ell.natAbs) :
    ‖packetResidueFormula q ell‖ = 1 := by
  rw [packetResidueFormula_eq_factor hq ell,
    packetResidueFactor_eq hq ell]
  simp [hd]

theorem norm_packetResidueFormula_of_not_dvd
    {q : ℕ} [NeZero q] (hq : Nat.Prime q) {ell : ℤ}
    (hd : ¬ q ∣ ell.natAbs) :
    ‖packetResidueFormula q ell‖ =
      1 / ((q : ℝ) - 1) := by
  rw [packetResidueFormula_eq_factor hq ell,
    packetResidueFactor_eq hq ell]
  simp [hd]
  have hqone : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hq.one_le
  have hcast :
      (q : ℂ) - 1 = ((((q : ℝ) - 1 : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hqone)]

/-- Off the divisibility set, every residual factor in the dyadic window is
bounded by `1/(Q-1)`. -/
theorem norm_packetResidueFormula_le_window
    {Q q : ℕ} (hQ : 2 ≤ Q) (hqmem : q ∈ packetPrimes Q)
    {ell : ℤ} (hd : ¬ q ∣ ell.natAbs) :
    ‖packetResidueFormula q ell‖ ≤
      1 / ((Q : ℝ) - 1) := by
  have hqdata := mem_packetPrimes_iff.mp hqmem
  have hqprime := hqdata.2.2
  letI : NeZero q := ⟨hqprime.ne_zero⟩
  rw [norm_packetResidueFormula_of_not_dvd hqprime hd]
  have hQone : (1 : ℝ) < (Q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hQ)
  have hdenQ : 0 < (Q : ℝ) - 1 := sub_pos.mpr hQone
  have hden :
      (Q : ℝ) - 1 ≤ (q : ℝ) - 1 := by
    exact sub_le_sub_right (by exact_mod_cast hqdata.1) 1
  exact one_div_le_one_div_of_le hdenQ hden

/-- Pointwise envelope separating the exceptional divisibility contribution
from the generic `1/(Q-1)` contribution. -/
theorem norm_packetResidueFormula_le_indicator_add
    {Q q : ℕ} (hQ : 2 ≤ Q) (hqmem : q ∈ packetPrimes Q)
    (ell : ℤ) :
    ‖packetResidueFormula q ell‖ ≤
      (if q ∣ ell.natAbs then (1 : ℝ) else 0) +
        1 / ((Q : ℝ) - 1) := by
  by_cases hd : q ∣ ell.natAbs
  · have hqprime := (mem_packetPrimes_iff.mp hqmem).2.2
    letI : NeZero q := ⟨hqprime.ne_zero⟩
    rw [norm_packetResidueFormula_of_dvd hqprime hd]
    simp only [hd, if_true]
    have hQone : (1 : ℝ) < (Q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hQ)
    exact le_add_of_nonneg_right
      (le_of_lt (one_div_pos.mpr (sub_pos.mpr hQone)))
  · simp only [hd, if_false, zero_add]
    exact norm_packetResidueFormula_le_window hQ hqmem hd

/-- Summed residue-factor estimate over the dyadic prime packet. -/
theorem sum_norm_packetResidueFormula_le
    {Q : ℕ} (hQ : 2 ≤ Q) (ell : ℤ) :
    (∑ q ∈ packetPrimes Q, ‖packetResidueFormula q ell‖) ≤
      ((packetPrimeDivisors Q ell.natAbs).card : ℝ) +
        ((packetPrimes Q).card : ℝ) /
          ((Q : ℝ) - 1) := by
  calc
    (∑ q ∈ packetPrimes Q, ‖packetResidueFormula q ell‖)
        ≤ ∑ q ∈ packetPrimes Q,
            ((if q ∣ ell.natAbs then (1 : ℝ) else 0) +
              1 / ((Q : ℝ) - 1)) := by
          apply Finset.sum_le_sum
          intro q hq
          exact norm_packetResidueFormula_le_indicator_add hQ hq ell
    _ = ((packetPrimeDivisors Q ell.natAbs).card : ℝ) +
          ((packetPrimes Q).card : ℝ) /
            ((Q : ℝ) - 1) := by
      rw [Finset.sum_add_distrib]
      have hind :
          (∑ q ∈ packetPrimes Q,
              (if q ∣ ell.natAbs then (1 : ℝ) else 0)) =
            ((packetPrimeDivisors Q ell.natAbs).card : ℝ) := by
        simp [packetPrimeDivisors]
      rw [hind]
      simp [div_eq_mul_inv, mul_comm]

end TNumbersLean
