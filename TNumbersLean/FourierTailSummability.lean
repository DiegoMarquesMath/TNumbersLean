import TNumbersLean.FourierSecondMoment
import TNumbersLean.StretchedExpSummability

namespace TNumbersLean

open Finset MeasureTheory
open scoped BigOperators

/-- The off-diagonal majorant produced by the lacunary Fourier estimate. -/
noncomputable def lacunaryFourierMomentTerm (C c : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) *
    (C * Real.exp
      (-c * (Real.log (2 + (2 : ℝ) ^ n)) ^ ((1 : ℝ) / 4)))

theorem lacunaryFourierMomentTerm_nonneg
    {C c : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ lacunaryFourierMomentTerm C c n := by
  unfold lacunaryFourierMomentTerm
  positivity

/-- The logarithmic lacunary majorant is bounded by an ordinary
stretched-exponential majorant with a positive rescaled constant. -/
theorem lacunaryFourierMomentTerm_le_stretched
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (n : ℕ) :
    lacunaryFourierMomentTerm C c n ≤
      C * stretchedExpMomentTerm
        (c * (Real.log 2) ^ ((1 : ℝ) / 4)) n := by
  have hlog2 : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hlog :
      (n : ℝ) * Real.log 2 ≤
        Real.log (2 + (2 : ℝ) ^ n) := by
    calc
      (n : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ n) := by
        rw [Real.log_pow]
      _ ≤ Real.log (2 + (2 : ℝ) ^ n) := by
        apply Real.log_le_log
        · positivity
        · linarith
  have hroot :
      (n : ℝ) ^ ((1 : ℝ) / 4) *
          (Real.log 2) ^ ((1 : ℝ) / 4) ≤
        (Real.log (2 + (2 : ℝ) ^ n)) ^ ((1 : ℝ) / 4) := by
    rw [← Real.mul_rpow (Nat.cast_nonneg n) hlog2]
    exact Real.rpow_le_rpow
      (mul_nonneg (Nat.cast_nonneg n) hlog2) hlog (by norm_num)
  have hexp :
      Real.exp
          (-c * (Real.log (2 + (2 : ℝ) ^ n)) ^ ((1 : ℝ) / 4)) ≤
        Real.exp
          (-(c * (Real.log 2) ^ ((1 : ℝ) / 4)) *
            (n : ℝ) ^ ((1 : ℝ) / 4)) := by
    apply Real.exp_le_exp.mpr
    calc
      -c * (Real.log (2 + (2 : ℝ) ^ n)) ^ ((1 : ℝ) / 4)
          ≤ -c *
              ((n : ℝ) ^ ((1 : ℝ) / 4) *
                (Real.log 2) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonpos_left hroot (by linarith)
      _ =
          -(c * (Real.log 2) ^ ((1 : ℝ) / 4)) *
            (n : ℝ) ^ ((1 : ℝ) / 4) := by
        ring
  have hCexp :
      C * Real.exp
          (-c * (Real.log (2 + (2 : ℝ) ^ n)) ^ ((1 : ℝ) / 4)) ≤
        C * Real.exp
          (-(c * (Real.log 2) ^ ((1 : ℝ) / 4)) *
            (n : ℝ) ^ ((1 : ℝ) / 4)) :=
    mul_le_mul_of_nonneg_left hexp hC
  have hnCexp :
      (n : ℝ) *
          (C * Real.exp
            (-c * (Real.log (2 + (2 : ℝ) ^ n)) ^ ((1 : ℝ) / 4))) ≤
        (n : ℝ) *
          (C * Real.exp
            (-(c * (Real.log 2) ^ ((1 : ℝ) / 4)) *
              (n : ℝ) ^ ((1 : ℝ) / 4))) :=
    mul_le_mul_of_nonneg_left hCexp (Nat.cast_nonneg n)
  rw [lacunaryFourierMomentTerm]
  calc
    (n : ℝ) *
        (C * Real.exp
          (-c * (Real.log (2 + (2 : ℝ) ^ n)) ^ ((1 : ℝ) / 4))) ≤
      (n : ℝ) *
        (C * Real.exp
          (-(c * (Real.log 2) ^ ((1 : ℝ) / 4)) *
            (n : ℝ) ^ ((1 : ℝ) / 4))) := hnCexp
    _ =
        C * stretchedExpMomentTerm
          (c * (Real.log 2) ^ ((1 : ℝ) / 4)) n := by
      rw [stretchedExpMomentTerm]
      ring

/-- The complete off-diagonal series in the second-moment estimate converges. -/
theorem summable_lacunaryFourierMomentTerm
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    Summable (lacunaryFourierMomentTerm C c) := by
  let κ : ℝ := c * (Real.log 2) ^ ((1 : ℝ) / 4)
  have hlog2 : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hκ : 0 < κ := by
    dsimp [κ]
    exact mul_pos hc (Real.rpow_pos_of_pos hlog2 _)
  have hsum :
      Summable (fun n : ℕ => C * stretchedExpMomentTerm κ n) :=
    (summable_stretchedExpMomentTerm hκ).mul_left C
  refine Summable.of_nonneg_of_le
    (fun n => lacunaryFourierMomentTerm_nonneg hC n) ?_ hsum
  intro n
  simpa [κ] using
    (lacunaryFourierMomentTerm_le_stretched
      (C := C) (c := c) hC hc.le n)

/-- The finite off-diagonal sum is bounded by the convergent full series. -/
theorem sum_lacunaryFourierMomentTerm_le_tsum
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (N : ℕ) :
    (∑ n ∈ Finset.range N, lacunaryFourierMomentTerm C c n) ≤
      ∑' n : ℕ, lacunaryFourierMomentTerm C c n := by
  exact (summable_lacunaryFourierMomentTerm hC hc).sum_le_tsum _
    (fun n _ => lacunaryFourierMomentTerm_nonneg hC n)

/-- A finite constant controlling all off-diagonal Weyl correlations. -/
noncomputable def fourierOffDiagonalConstant (C c : ℝ) : ℝ :=
  2 * ∑' n : ℕ, lacunaryFourierMomentTerm C c n

theorem fourierOffDiagonalConstant_nonneg
    {C c : ℝ} (hC : 0 ≤ C) :
    0 ≤ fourierOffDiagonalConstant C c := by
  unfold fourierOffDiagonalConstant
  exact mul_nonneg (by norm_num)
    (tsum_nonneg fun n => lacunaryFourierMomentTerm_nonneg hC n)

/-- Uniform linear second-moment estimate:
the Fourier-decay hypothesis gives ∫|S_N|² dμ ≤ N + K. -/
theorem weylSecondMoment_le_linear
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c)
    {b : ℕ} (hb : 2 ≤ b) {h : ℤ} (hh : h ≠ 0) (N : ℕ) :
    weylSecondMoment μ b h N ≤
      (N : ℝ) + fourierOffDiagonalConstant C c := by
  rcases hdecay with ⟨hC, hc, hbound⟩
  have hdecay' : HasPaperFourierDecay μ C c := ⟨hC, hc, hbound⟩
  calc
    weylSecondMoment μ b h N
        ≤ (N : ℝ) +
            2 * ∑ r ∈ Finset.range N,
              (r : ℝ) *
                (C * Real.exp
                  (-c * (Real.log (2 + (2 : ℝ) ^ r)) ^
                    ((1 : ℝ) / 4))) :=
      weylSecondMoment_le_decay_triangle hdecay' hb hh N
    _ = (N : ℝ) +
          2 * ∑ r ∈ Finset.range N,
            lacunaryFourierMomentTerm C c r := by
      simp only [lacunaryFourierMomentTerm]
    _ ≤ (N : ℝ) +
          2 * ∑' r : ℕ, lacunaryFourierMomentTerm C c r := by
      gcongr
      exact sum_lacunaryFourierMomentTerm_le_tsum hC.le hc N
    _ = (N : ℝ) + fourierOffDiagonalConstant C c := by
      rfl

end TNumbersLean
