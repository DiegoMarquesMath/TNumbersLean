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
    |t - (round t : ℝ)| ≤ (1 / 2 : ℝ) := by
  exact abs_sub_round t

/-- Distance comparison after recentering the integer lattice at the nearest
integer to `t`. -/
theorem one_add_abs_int_le_two_mul_one_add_abs_shift
    (t : ℝ) (j : ℤ) :
    1 + |(j : ℝ)| ≤
      2 * (1 + |t - ((round t + j : ℤ) : ℝ)|) := by
  have hr := abs_sub_round_real t
  have htriangle :
      |(j : ℝ)| ≤
        |t - ((round t + j : ℤ) : ℝ)| +
          |t - (round t : ℝ)| := by
    have hid :
        (j : ℝ) =
          (t - (round t : ℝ)) -
            (t - ((round t + j : ℤ) : ℝ)) := by
      push_cast
      ring
    rw [hid]
    have htri :=
      abs_add (t - (round t : ℝ))
        (-(t - ((round t + j : ℤ) : ℝ)))
    simpa [sub_eq_add_neg, abs_neg, add_comm] using htri
  nlinarith [abs_nonneg (t - ((round t + j : ℤ) : ℝ))]

/-- Uniform comparison of shifted power kernels with the fixed 3/2 lattice
kernel. -/
theorem shifted_power_kernel_le_base
    {s t : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ (1 / 2 : ℝ))
    (j : ℤ) :
    (1 + |t - ((round t + j : ℤ) : ℝ)|) ^ (-(2 - s)) ≤
      4 * packetBaseKernel j := by
  have hp : (3 / 2 : ℝ) ≤ 2 - s := by linarith
  have hdist :
      (1 + |(j : ℝ)|) / 2 ≤
        1 + |t - ((round t + j : ℤ) : ℝ)| := by
    have h := one_add_abs_int_le_two_mul_one_add_abs_shift t j
    linarith
  have hleft : 0 < (1 + |(j : ℝ)|) / 2 := by positivity
  have hneg : -(2 - s) ≤ 0 := by linarith
  have hbasecomp :
      (1 + |t - ((round t + j : ℤ) : ℝ)|) ^ (-(2 - s)) ≤
        ((1 + |(j : ℝ)|) / 2) ^ (-(2 - s)) :=
    Real.rpow_le_rpow_of_nonpos hleft hdist hneg
  let B : ℝ := 1 + |(j : ℝ)|
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [abs_nonneg (j : ℝ)]
  have hexp : -(2 - s) ≤ -(3 / 2 : ℝ) := by linarith
  have hBpow :
      B ^ (-(2 - s)) ≤ B ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hB hexp
  have htwoexp : 2 - s ≤ (2 : ℝ) := by linarith
  have htwo : (2 : ℝ) ^ (2 - s) ≤ 4 := by
    calc
      (2 : ℝ) ^ (2 - s) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) htwoexp
      _ = 4 := by norm_num
  have hsplit :
      (B / 2) ^ (-(2 - s)) =
        (2 : ℝ) ^ (2 - s) * B ^ (-(2 - s)) := by
    rw [Real.div_rpow (by positivity) (by norm_num)]
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by norm_num)]
    simp [div_eq_mul_inv, mul_comm]
  calc
    (1 + |t - ((round t + j : ℤ) : ℝ)|) ^ (-(2 - s))
        ≤ ((1 + |(j : ℝ)|) / 2) ^ (-(2 - s)) := hbasecomp
    _ = (2 : ℝ) ^ (2 - s) * B ^ (-(2 - s)) := by
          simpa [B] using hsplit
    _ ≤ 4 * B ^ (-(2 - s)) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (by positivity) _)
    _ ≤ 4 * B ^ (-(3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hBpow (by norm_num)
    _ = 4 * packetBaseKernel j := by
      rfl

/-- Shifted power kernel appearing after the standard weighted convolution
inequality. -/
noncomputable def packetShiftedKernel (s t : ℝ) (ell : ℤ) : ℝ :=
  (1 + |t - (ell : ℝ)|) ^ (-(2 - s))

theorem packetShiftedKernel_nonneg (s t : ℝ) (ell : ℤ) :
    0 ≤ packetShiftedKernel s t ell := by
  exact Real.rpow_nonneg (by positivity) _

/-- For every admissible weight exponent, the shifted lattice kernel is
summable uniformly in the real shift. -/
theorem summable_packetShiftedKernel
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ (1 / 2 : ℝ))
    (t : ℝ) :
    Summable (packetShiftedKernel s t) := by
  have hcenter :
      Summable (fun j : ℤ =>
        packetShiftedKernel s t (round t + j)) := by
    refine Summable.of_nonneg_of_le
      (fun j => packetShiftedKernel_nonneg s t (round t + j))
      (fun j => ?_)
      (summable_packetBaseKernel.mul_left 4)
    simpa [packetShiftedKernel] using
      shifted_power_kernel_le_base (t := t) hs0 hs j
  have hcenter' :
      Summable (fun j : ℤ =>
        packetShiftedKernel s t
          (Equiv.addRight (round t) j)) := by
    simpa [Equiv.coe_addRight, add_comm] using hcenter
  exact (Equiv.addRight (round t)).summable_iff.mp hcenter'

/-- Uniform bound for the full shifted lattice sum. -/
theorem tsum_packetShiftedKernel_le
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ (1 / 2 : ℝ))
    (t : ℝ) :
    (∑' ell : ℤ, packetShiftedKernel s t ell) ≤
      packetConvolutionConstant := by
  have hcenter :
      Summable (fun j : ℤ =>
        packetShiftedKernel s t (round t + j)) :=
    Summable.of_nonneg_of_le
      (fun j => packetShiftedKernel_nonneg s t (round t + j))
      (fun j => by
        simpa [packetShiftedKernel] using
          shifted_power_kernel_le_base (t := t) hs0 hs j)
      (summable_packetBaseKernel.mul_left 4)
  have hbound :
      (∑' j : ℤ,
        packetShiftedKernel s t (round t + j)) ≤
        packetConvolutionConstant := by
    have h :=
      hcenter.tsum_le_tsum
        (fun j => by
          simpa [packetShiftedKernel] using
            shifted_power_kernel_le_base (t := t) hs0 hs j)
        (summable_packetBaseKernel.mul_left 4)
    simpa [packetConvolutionConstant, tsum_mul_left] using h
  have hreindex :=
    (Equiv.addRight (round t)).tsum_eq
      (f := packetShiftedKernel s t)
  calc
    (∑' ell : ℤ, packetShiftedKernel s t ell)
        = ∑' j : ℤ,
            packetShiftedKernel s t
              (Equiv.addRight (round t) j) := hreindex.symm
    _ = ∑' j : ℤ,
          packetShiftedKernel s t (round t + j) := by
          apply tsum_congr
          intro j
          simp [Equiv.coe_addRight, add_comm]
    _ ≤ packetConvolutionConstant := hbound

end TNumbersLean
