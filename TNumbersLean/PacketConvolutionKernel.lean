import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import TNumbersLean.WeightedAveragedPacketCoefficient

namespace TNumbersLean

open scoped BigOperators

/-- Universal comparison kernel for the discrete convolution step in the
packet lemma. -/
noncomputable def packetBaseKernel (j : ℤ) : ℝ :=
  (1 + |(j : ℝ)|) ^ (-(3 / 2 : ℝ))

theorem packetBaseKernel_nonneg (j : ℤ) :
    0 ≤ packetBaseKernel j := by
  exact Real.rpow_nonneg (by positivity) _

/-- The universal lattice kernel with exponent 3/2 is summable. -/
theorem summable_packetBaseKernel :
    Summable packetBaseKernel := by
  have hp :
      Summable (fun j : ℤ => |(j : ℝ)| ^ (-(3 / 2 : ℝ))) :=
    Real.summable_abs_int_rpow (by norm_num)
  have hdelta :
      Summable (fun j : ℤ => if j = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  have hmajor :
      Summable (fun j : ℤ =>
        (if j = 0 then (1 : ℝ) else 0) +
          |(j : ℝ)| ^ (-(3 / 2 : ℝ))) :=
    hdelta.add hp
  refine Summable.of_nonneg_of_le packetBaseKernel_nonneg ?_ hmajor
  intro j
  by_cases hj : j = 0
  · subst j
    simp [packetBaseKernel]
  · simp only [hj, if_false, zero_add]
    unfold packetBaseKernel
    have habspos : 0 < |(j : ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
    have hbase : |(j : ℝ)| ≤ 1 + |(j : ℝ)| := by linarith
    exact Real.rpow_le_rpow_of_nonpos habspos hbase (by norm_num)

/-- A fixed finite constant dominating all shifted convolution kernels used
below. -/
noncomputable def packetConvolutionConstant : ℝ :=
  4 * ∑' j : ℤ, packetBaseKernel j

theorem packetConvolutionConstant_nonneg :
    0 ≤ packetConvolutionConstant := by
  unfold packetConvolutionConstant
  exact mul_nonneg (by norm_num)
    (tsum_nonneg packetBaseKernel_nonneg)

/-- Every real number is within one half of its nearest integer. -/
theorem abs_sub_round_real (t : ℝ) :
    |t - (Int.round t : ℝ)| ≤ (1 / 2 : ℝ) := by
  exact Int.abs_sub_round t

/-- Distance comparison after recentering the integer lattice at the nearest
integer to `t`. -/
theorem one_add_abs_int_le_two_mul_one_add_abs_shift
    (t : ℝ) (j : ℤ) :
    1 + |(j : ℝ)| ≤
      2 * (1 + |t - ((Int.round t + j : ℤ) : ℝ)|) := by
  have hr := abs_sub_round_real t
  have htriangle :
      |(j : ℝ)| ≤
        |t - ((Int.round t + j : ℤ) : ℝ)| +
          |t - (Int.round t : ℝ)| := by
    have hid :
        (j : ℝ) =
          (t - (Int.round t : ℝ)) -
            (t - ((Int.round t + j : ℤ) : ℝ)) := by
      push_cast
      ring
    rw [hid]
    exact abs_sub _ _
  nlinarith [abs_nonneg (t - ((Int.round t + j : ℤ) : ℝ))]

/-- Uniform comparison of shifted power kernels with the fixed 3/2 lattice
kernel. -/
theorem shifted_power_kernel_le_base
    {s t : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ (1 / 2 : ℝ))
    (j : ℤ) :
    (1 + |t - ((Int.round t + j : ℤ) : ℝ)|) ^ (-(2 - s)) ≤
      4 * packetBaseKernel j := by
  have hp : (3 / 2 : ℝ) ≤ 2 - s := by linarith
  have hdist :
      (1 + |(j : ℝ)|) / 2 ≤
        1 + |t - ((Int.round t + j : ℤ) : ℝ)| := by
    have h := one_add_abs_int_le_two_mul_one_add_abs_shift t j
    linarith
  have hleft : 0 < (1 + |(j : ℝ)|) / 2 := by positivity
  have hneg : -(2 - s) ≤ 0 := by linarith
  have hbasecomp :
      (1 + |t - ((Int.round t + j : ℤ) : ℝ)|) ^ (-(2 - s)) ≤
        ((1 + |(j : ℝ)|) / 2) ^ (-(2 - s)) :=
    Real.rpow_le_rpow_of_nonpos hleft hdist hneg
  have hpowexp :
      ((1 + |(j : ℝ)|) / 2) ^ (-(2 - s)) ≤
        ((1 + |(j : ℝ)|) / 2) ^ (-(3 / 2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · positivity
    · linarith
  have hsplit :
      ((1 + |(j : ℝ)|) / 2) ^ (-(3 / 2 : ℝ)) =
        (2 : ℝ) ^ (3 / 2 : ℝ) * packetBaseKernel j := by
    unfold packetBaseKernel
    rw [div_rpow (by positivity) (by norm_num)]
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by norm_num)]
    field_simp
    rw [← Real.rpow_neg (by norm_num)]
  have htwo : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
    calc
      (2 : ℝ) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  calc
    (1 + |t - ((Int.round t + j : ℤ) : ℝ)|) ^ (-(2 - s))
        ≤ ((1 + |(j : ℝ)|) / 2) ^ (-(2 - s)) := hbasecomp
    _ ≤ ((1 + |(j : ℝ)|) / 2) ^ (-(3 / 2 : ℝ)) := hpowexp
    _ = (2 : ℝ) ^ (3 / 2 : ℝ) * packetBaseKernel j := hsplit
    _ ≤ 4 * packetBaseKernel j :=
      mul_le_mul_of_nonneg_right htwo (packetBaseKernel_nonneg j)

end TNumbersLean
