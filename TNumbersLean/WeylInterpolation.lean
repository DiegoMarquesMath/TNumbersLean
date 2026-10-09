import TNumbersLean.NormalityFromFourier

namespace TNumbersLean

open Filter Finset MeasureTheory
open scoped BigOperators Topology

/-- The norm of the normalized Weyl sum is the ordinary Weyl-sum norm
divided by the length. -/
theorem norm_normalizedWeylSum_eq_div
    (b : ℕ) (h : ℤ) (x : ℝ) (N : ℕ) :
    ‖normalizedWeylSum b h x N‖ =
      ‖weylSum b h x N‖ / (N : ℝ) := by
  simp [normalizedWeylSum, norm_inv, div_eq_mul_inv, mul_comm]

/-- Interpolation from the square subsequence, already normalized by N.
The right-hand side is precisely the square-gap error plus the normalized
square-subsequence error. -/
theorem norm_normalizedWeylSum_le_square_terms
    (b : ℕ) (h : ℤ) (x : ℝ) {N : ℕ} (hN : 0 < N) :
    ‖normalizedWeylSum b h x N‖ ≤
      squareGapRatio (Nat.sqrt N) +
        squareNormRatio
          (fun M y => weylSum b h y M) x (Nat.sqrt N) := by
  let j : ℕ := Nat.sqrt N
  have hjpos : 0 < j := by
    dsimp [j]
    exact Nat.sqrt_pos.mpr hN
  have hjrpos : (0 : ℝ) < j := by
    exact_mod_cast hjpos
  have hjr2pos : (0 : ℝ) < (j : ℝ) ^ 2 :=
    sq_pos_of_pos hjrpos
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hj2leN : (j : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast (nat_sqrt_square_bounds N).1
  have hsq :
      ‖weylSum b h x (j ^ 2)‖ ≤
        squareNormRatio
            (fun M y => weylSum b h y M) x j *
          (j : ℝ) ^ 2 := by
    rw [squareNormRatio]
    rw [div_mul_cancel₀ _ (ne_of_gt hjr2pos)]
  have hinterp :
      ‖weylSum b h x N‖ ≤
        ((2 * j + 1 : ℕ) : ℝ) +
          squareNormRatio
              (fun M y => weylSum b h y M) x j *
            (j : ℝ) ^ 2 := by
    simpa [j] using
      (norm_weylSum_sqrt_interpolation
        b h x N
        (ε :=
          squareNormRatio
            (fun M y => weylSum b h y M) x (Nat.sqrt N))
        (by simpa [j] using hsq))
  have hbound_nonneg :
      0 ≤
        ((2 * j + 1 : ℕ) : ℝ) +
          squareNormRatio
              (fun M y => weylSum b h y M) x j *
            (j : ℝ) ^ 2 := by
    exact add_nonneg (Nat.cast_nonneg _)
      (mul_nonneg
        (squareNormRatio_nonneg
          (fun M y => weylSum b h y M) x j)
        (sq_nonneg _))
  calc
    ‖normalizedWeylSum b h x N‖
        = ‖weylSum b h x N‖ / (N : ℝ) :=
      norm_normalizedWeylSum_eq_div b h x N
    _ ≤
        (((2 * j + 1 : ℕ) : ℝ) +
          squareNormRatio
              (fun M y => weylSum b h y M) x j *
            (j : ℝ) ^ 2) / (N : ℝ) :=
      (div_le_div_iff_of_pos_right hNreal).2 hinterp
    _ ≤
        (((2 * j + 1 : ℕ) : ℝ) +
          squareNormRatio
              (fun M y => weylSum b h y M) x j *
            (j : ℝ) ^ 2) / (j : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hbound_nonneg hjr2pos hj2leN
    _ =
        ((2 * j + 1 : ℕ) : ℝ) / (j : ℝ) ^ 2 +
          squareNormRatio
            (fun M y => weylSum b h y M) x j := by
      field_simp [ne_of_gt hjrpos]
    _ =
        squareGapRatio (Nat.sqrt N) +
          squareNormRatio
            (fun M y => weylSum b h y M) x (Nat.sqrt N) := by
      simp only [j, squareGapRatio]

/-- Convergence on the square subsequence implies convergence of the full
normalized Weyl sums.  This packages the square-gap interpolation step of
the manuscript. -/
theorem normalizedWeylSum_tendsto_zero_of_squareNormRatio
    (b : ℕ) (h : ℤ) (x : ℝ)
    (hsq :
      Tendsto
        (squareNormRatio
          (fun N y => weylSum b h y N) x)
        atTop (𝓝 0)) :
    Tendsto
      (fun N : ℕ => normalizedWeylSum b h x N)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hratio :
      Tendsto
        (fun N : ℕ =>
          squareNormRatio
            (fun M y => weylSum b h y M) x (Nat.sqrt N))
        atTop (𝓝 0) :=
    hsq.comp natSqrt_tendsto_atTop
  have hupper :
      Tendsto
        (fun N : ℕ =>
          squareGapRatio (Nat.sqrt N) +
            squareNormRatio
              (fun M y => weylSum b h y M) x (Nat.sqrt N))
        atTop (𝓝 0) := by
    simpa using squareGapRatio_sqrt_tendsto_zero.add hratio
  apply squeeze_zero'
  · exact Eventually.of_forall fun N =>
      norm_nonneg (normalizedWeylSum b h x N)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    exact norm_normalizedWeylSum_le_square_terms b h x hN
  · exact hupper

end TNumbersLean
