import Mathlib.Analysis.Normed.Group.Int
import TNumbersLean.AveragedPacketCoefficientBound
import TNumbersLean.WeightedPacketElementary

namespace TNumbersLean

/-- Integer absolute value and natAbs agree after casting to the reals. -/
theorem natAbs_cast_real_eq_abs_intCast (ell : ℤ) :
    (ell.natAbs : ℝ) = |(ell : ℝ)| := by
  have hz : (ell.natAbs : ℤ) = |ell| := Int.natCast_natAbs ell
  have hr := congrArg (fun z : ℤ => (z : ℝ)) hz
  convert hr using 1
  norm_cast

/-- Weighted form of the averaged-packet coefficient estimate, before
specializing s and X to the manuscript scales. -/
theorem weighted_averagedPacketCoeffFormula_le
    (H : PrimePacketCountInputs)
    {Q A : ℕ} (hQ : H.threshold ≤ Q) (hA : 2 ≤ A)
    (θ₀ : ℝ) {ell : ℤ} (hell : ell ≠ 0)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ (1 / 2 : ℝ)) :
    (1 + |(ell : ℝ)|) ^ s *
        ‖averagedPacketCoeffFormula Q A θ₀ ell‖ ≤
      4 * averagedPacketFourierConstant H / (Q : ℝ) *
        ((((2 * Q : ℕ) : ℝ) ^ A) ^ s) *
        Real.log (2 + (((2 * Q : ℕ) : ℝ) ^ A)) := by
  have hQtwo : 2 ≤ Q := H.threshold_ge_two.trans hQ
  have hbase : (2 : ℝ) ≤ ((2 * Q : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ 2 * Q by omega)
  have hb1 : (1 : ℝ) ≤ ((2 * Q : ℕ) : ℝ) :=
    le_trans (by norm_num) hbase
  have hpow : (1 : ℝ) ≤ (((2 * Q : ℕ) : ℝ) ^ (A - 1)) :=
    one_le_pow₀ hb1
  have hAeq : A = (A - 1) + 1 := by omega
  have hX :
      (2 : ℝ) ≤ (((2 * Q : ℕ) : ℝ) ^ A) := by
    calc
      (2 : ℝ) ≤ ((2 * Q : ℕ) : ℝ) := hbase
      _ ≤ (((2 * Q : ℕ) : ℝ) ^ (A - 1)) *
            ((2 * Q : ℕ) : ℝ) := by
          nlinarith
      _ = (((2 * Q : ℕ) : ℝ) ^ ((A - 1) + 1)) := by
          rw [pow_succ]
      _ = (((2 * Q : ℕ) : ℝ) ^ A) := by
          rw [← hAeq]
  have habs := natAbs_cast_real_eq_abs_intCast ell
  have hcoeff :=
    norm_averagedPacketCoeffFormula_le_logarithmic
      (A := A) H hQ θ₀ hell
  rw [habs] at hcoeff
  have helem :=
    weighted_packet_elementary
      hs0 hs hX (abs_nonneg (ell : ℝ))
  have hC : 0 ≤ averagedPacketFourierConstant H :=
    averagedPacketFourierConstant_nonneg H
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hQtwo)
  have hweight : 0 ≤ (1 + |(ell : ℝ)|) ^ s :=
    Real.rpow_nonneg (by positivity) s
  calc
    (1 + |(ell : ℝ)|) ^ s *
        ‖averagedPacketCoeffFormula Q A θ₀ ell‖
        ≤ (1 + |(ell : ℝ)|) ^ s *
          (averagedPacketFourierConstant H *
            Real.log (2 + |(ell : ℝ)|) / (Q : ℝ) /
            (1 + |(ell : ℝ)| /
              (((2 * Q : ℕ) : ℝ) ^ A)) ^ 2) :=
      mul_le_mul_of_nonneg_left hcoeff hweight
    _ = (averagedPacketFourierConstant H / (Q : ℝ)) *
          ((1 + |(ell : ℝ)|) ^ s *
            Real.log (2 + |(ell : ℝ)|) /
            (1 + |(ell : ℝ)| /
              (((2 * Q : ℕ) : ℝ) ^ A)) ^ 2) := by
          ring
    _ ≤ (averagedPacketFourierConstant H / (Q : ℝ)) *
          (4 * ((((2 * Q : ℕ) : ℝ) ^ A) ^ s) *
            Real.log (2 + (((2 * Q : ℕ) : ℝ) ^ A))) := by
          exact mul_le_mul_of_nonneg_left helem
            (div_nonneg hC hQpos.le)
    _ = 4 * averagedPacketFourierConstant H / (Q : ℝ) *
          ((((2 * Q : ℕ) : ℝ) ^ A) ^ s) *
          Real.log (2 + (((2 * Q : ℕ) : ℝ) ^ A)) := by
          ring

end TNumbersLean
