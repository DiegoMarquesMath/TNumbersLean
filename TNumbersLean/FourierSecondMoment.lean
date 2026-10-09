import TNumbersLean.NormalityFromFourier
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

namespace TNumbersLean

open Complex MeasureTheory Finset
open scoped BigOperators ComplexConjugate

/-- The Fourier transform convention used in the manuscript:
    \hat μ(t) = ∫ exp(-2π i t x) dμ(x). -/
noncomputable def paperFourier (μ : Measure ℝ) (t : ℝ) : ℂ :=
  MeasureTheory.charFun μ (-2 * Real.pi * t)

theorem paperFourier_apply (μ : Measure ℝ) (t : ℝ) :
    paperFourier μ t =
      ∫ x : ℝ, circleExp (-2 * Real.pi * t * x) ∂μ := by
  rw [paperFourier, MeasureTheory.charFun_apply_real]
  apply integral_congr_ae
  filter_upwards with x
  simp only [circleExp]
  congr 1
  push_cast
  ring

@[simp]
theorem conj_circleExp (t : ℝ) :
    conj (circleExp t) = circleExp (-t) := by
  rw [circleExp, circleExp, ← Complex.exp_conj]
  congr 1
  simp

theorem circleExp_add (u v : ℝ) :
    circleExp u * circleExp v = circleExp (u + v) := by
  rw [circleExp, circleExp, circleExp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The manuscript frequency h(b^r-b^s) attached to a correlation term. -/
noncomputable def weylFrequency (b : ℕ) (h : ℤ) (r s : ℕ) : ℝ :=
  (h : ℝ) * ((b : ℝ) ^ r - (b : ℝ) ^ s)

theorem conj_weylTerm_mul_weylTerm
    (b r s : ℕ) (h : ℤ) (x : ℝ) :
    conj (weylTerm b r h x) * weylTerm b s h x =
      circleExp (-2 * Real.pi * weylFrequency b h r s * x) := by
  rw [weylTerm, weylTerm, conj_circleExp, circleExp_add]
  congr 1
  simp only [weylFrequency]
  ring

/-- Each individual Weyl correlation is integrable against a finite measure. -/
theorem integrable_weylCorrelation
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (b r s : ℕ) (h : ℤ) :
    Integrable (fun x : ℝ => conj (weylTerm b r h x) * weylTerm b s h x) μ := by
  refine Integrable.of_bound ?_ 1 ?_
  · apply Continuous.aestronglyMeasurable
    unfold weylTerm circleExp
    fun_prop
  · filter_upwards with x
    simp

/-- A single correlation integrates to the manuscript Fourier transform
at the difference frequency. -/
theorem integral_weylCorrelation
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (b r s : ℕ) (h : ℤ) :
    (∫ x : ℝ, conj (weylTerm b r h x) * weylTerm b s h x ∂μ) =
      paperFourier μ (weylFrequency b h r s) := by
  rw [paperFourier_apply]
  apply integral_congr_ae
  filter_upwards with x
  exact conj_weylTerm_mul_weylTerm b r s h x

/-- Pointwise expansion of |S_N|^2 into the double correlation sum. -/
theorem ofReal_normSq_weylSum_eq_doubleSum
    (b N : ℕ) (h : ℤ) (x : ℝ) :
    ((‖weylSum b h x N‖ ^ 2 : ℝ) : ℂ) =
      ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        conj (weylTerm b (r + 1) h x) * weylTerm b (s + 1) h x := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [weylSum, map_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]

/-- Exact finite second-moment identity before separating diagonal and
off-diagonal terms. -/
theorem integral_normSq_weylSum_eq_doubleFourier
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (b N : ℕ) (h : ℤ) :
    (∫ x : ℝ, ((‖weylSum b h x N‖ ^ 2 : ℝ) : ℂ) ∂μ) =
      ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        paperFourier μ (weylFrequency b h (r + 1) (s + 1)) := by
  rw [integral_congr_ae (ae_of_all μ fun x =>
    ofReal_normSq_weylSum_eq_doubleSum b N h x)]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro s hs
      exact integral_weylCorrelation b (r + 1) (s + 1) h
    · intro s hs
      exact integrable_weylCorrelation b (r + 1) (s + 1) h
  · intro r hr
    exact integrable_finsetSum' _ fun s hs =>
      integrable_weylCorrelation b (r + 1) (s + 1) h

end TNumbersLean
