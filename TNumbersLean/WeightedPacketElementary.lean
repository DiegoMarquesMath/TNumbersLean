import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace TNumbersLean

/-- Elementary weighted estimate used after the averaged-packet Fourier
coefficient bound. The constant 4 is deliberately non-optimal. -/
theorem weighted_packet_elementary
    {s X y : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ (1 / 2 : ℝ))
    (hX : 2 ≤ X) (hy : 0 ≤ y) :
    (1 + y) ^ s * Real.log (2 + y) /
        (1 + y / X) ^ 2 ≤
      4 * X ^ s * Real.log (2 + X) := by
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hlogX : 1 ≤ Real.log (2 + X) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_three.le.trans (by linarith)
  by_cases hyX : y ≤ X
  · have h1y : 0 ≤ 1 + y := by linarith
    have hbase : 1 + y ≤ 2 * X := by linarith
    have hrpow :
        (1 + y) ^ s ≤ (2 * X) ^ s :=
      Real.rpow_le_rpow h1y hbase hs0
    have hsplit : (2 * X) ^ s = (2 : ℝ) ^ s * X ^ s := by
      rw [Real.mul_rpow (by positivity) hX0.le]
    have h2s : (2 : ℝ) ^ s ≤ 2 := by
      calc
        (2 : ℝ) ^ s ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (hs.trans (by norm_num))
        _ = 2 := by simp
    have hlog :
        Real.log (2 + y) ≤ Real.log (2 + X) := by
      exact Real.log_le_log (by linarith) (by linarith)
    have hydiv : 0 ≤ y / X := div_nonneg hy hX0.le
    have hden : 1 ≤ (1 + y / X) ^ 2 := by
      nlinarith [sq_nonneg (y / X)]
    have hnum_nonneg : 0 ≤ (1 + y) ^ s * Real.log (2 + y) := by
      exact mul_nonneg (Real.rpow_nonneg h1y s)
        (Real.log_nonneg (by linarith))
    calc
      (1 + y) ^ s * Real.log (2 + y) /
          (1 + y / X) ^ 2
          ≤ (1 + y) ^ s * Real.log (2 + y) := by
            exact div_le_self hnum_nonneg hden
      _ ≤ (2 * X) ^ s * Real.log (2 + X) := by
            gcongr
      _ = (2 : ℝ) ^ s * X ^ s * Real.log (2 + X) := by rw [hsplit]
      _ ≤ 4 * X ^ s * Real.log (2 + X) := by
            have hXs : 0 ≤ X ^ s := Real.rpow_nonneg hX0.le s
            have hlognonneg : 0 ≤ Real.log (2 + X) := by linarith
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right h2s hXs)
              hlognonneg
  · have hyX' : X < y := lt_of_not_ge hyX
    let v : ℝ := y / X
    have hv : 1 ≤ v := by
      dsimp [v]
      exact (le_div_iff₀ hX0).2 (by simpa using hyX'.le)
    have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
    have hy_eq : y = X * v := by
      dsimp [v]
      field_simp [hX0.ne']
    have hbase : 1 + y ≤ 2 * X * v := by
      rw [hy_eq]
      have hXv : 1 ≤ X * v := by nlinarith
      linarith
    have hbase0 : 0 ≤ 1 + y := by linarith
    have hrpow :
        (1 + y) ^ s ≤ (2 * X * v) ^ s :=
      Real.rpow_le_rpow hbase0 hbase hs0
    have hsplit :
        (2 * X * v) ^ s = (2 : ℝ) ^ s * X ^ s * v ^ s := by
      rw [Real.mul_rpow (mul_nonneg (by norm_num) hX0.le) hv0.le,
        Real.mul_rpow (by norm_num) hX0.le]
    have h2s : (2 : ℝ) ^ s ≤ 2 := by
      calc
        (2 : ℝ) ^ s ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (hs.trans (by norm_num))
        _ = 2 := by simp
    have hvs : v ^ s ≤ v ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hv hs
    have hlogprod :
        Real.log (2 + y) ≤ Real.log (2 + X) + Real.log v := by
      rw [hy_eq]
      have hprod : 2 + X * v ≤ (2 + X) * v := by nlinarith
      calc
        Real.log (2 + X * v) ≤ Real.log ((2 + X) * v) :=
          Real.log_le_log (by positivity) hprod
        _ = Real.log (2 + X) + Real.log v := by
          rw [Real.log_mul (by linarith) hv0.ne']
    have hlogv : Real.log v ≤ v := Real.log_le_self hv0.le
    have hsqrt :
        v ^ (1 / 2 : ℝ) ≤ v := by
      calc
        v ^ (1 / 2 : ℝ) ≤ v ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
        _ = v := by simp
    have hden :
        v ^ 2 ≤ (1 + v) ^ 2 := by nlinarith
    have hvpowpos : 0 < v ^ 2 := by positivity
    rw [hy_eq, mul_div_cancel_left₀ _ hX0.ne']
    have hnum :
        (1 + X * v) ^ s * Real.log (2 + X * v) ≤
          4 * X ^ s * Real.log (2 + X) * v ^ 2 := by
      calc
        (1 + X * v) ^ s * Real.log (2 + X * v)
            ≤ (2 * X * v) ^ s *
                (Real.log (2 + X) + Real.log v) := by
              exact mul_le_mul hrpow hlogprod
                (Real.log_nonneg (by positivity))
                (Real.rpow_nonneg hbase0 s)
        _ = (2 : ℝ) ^ s * X ^ s * v ^ s *
              (Real.log (2 + X) + Real.log v) := by rw [hsplit]
        _ ≤ 4 * X ^ s * Real.log (2 + X) * v ^ 2 := by
              have hXs : 0 ≤ X ^ s := Real.rpow_nonneg hX0.le s
              have hvs0 : 0 ≤ v ^ s := Real.rpow_nonneg hv0.le s
              have hlogv0 : 0 ≤ Real.log v := Real.log_nonneg hv
              have hlogX0 : 0 ≤ Real.log (2 + X) := by linarith
              have hv_bound : v ^ s ≤ v := hvs.trans hsqrt
              have hlogv_bound :
                  Real.log v ≤ Real.log (2 + X) * v := by
                calc
                  Real.log v ≤ v := hlogv
                  _ ≤ Real.log (2 + X) * v := by
                    exact le_mul_of_one_le_left (by positivity) hlogX
              nlinarith
    calc
      (1 + X * v) ^ s * Real.log (2 + X * v) /
          (1 + v) ^ 2
          ≤ (1 + X * v) ^ s * Real.log (2 + X * v) /
              v ^ 2 := by
            exact div_le_div_of_nonneg_left
              (mul_nonneg (Real.rpow_nonneg (by positivity) s)
                (Real.log_nonneg (by positivity)))
              hvpowpos hden
      _ ≤ (4 * X ^ s * Real.log (2 + X) * v ^ 2) / v ^ 2 := by
            exact div_le_div_of_nonneg_right hnum hvpowpos.le
      _ = 4 * X ^ s * Real.log (2 + X) := by
            field_simp [ne_of_gt hvpowpos]

end TNumbersLean
