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


@[simp]
theorem weylFrequency_diag (b r : ℕ) (h : ℤ) :
    weylFrequency b h r r = 0 := by
  simp [weylFrequency]

@[simp]
theorem paperFourier_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    paperFourier μ 0 = 1 := by
  simp [paperFourier]

/-- The elementary lacunary separation used in Section 6:
for b ≥ 2 and 1 ≤ m < r, the power difference is at least 2^(r-1). -/
theorem two_pow_le_pow_sub_pow
    {b m r : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) (hmr : m < r) :
    2 ^ (r - 1) ≤ b ^ r - b ^ m := by
  have hr : 1 ≤ r := hm.trans hmr.le
  have hmr' : m ≤ r - 1 := by omega
  have hbase : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
  have hpowm : b ^ m ≤ b ^ (r - 1) :=
    pow_le_pow_right' hbase hmr'
  have hpow2 : 2 ^ (r - 1) ≤ b ^ (r - 1) :=
    pow_le_pow_left' hb (r - 1)
  have hr_eq : r = (r - 1) + 1 := by omega
  have htwice : 2 * b ^ (r - 1) ≤ b ^ r := by
    rw [hr_eq, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ hb
  omega

/-- The exact frequency lower bound in the normality argument:
|h(b^r-b^m)| ≥ 2^(r-1) for b ≥ 2, h ≠ 0, and 1 ≤ m < r. -/
theorem abs_weylFrequency_lower_bound
    {b m r : ℕ} {h : ℤ}
    (hb : 2 ≤ b) (hh : h ≠ 0) (hm : 1 ≤ m) (hmr : m < r) :
    (2 : ℝ) ^ (r - 1) ≤ |weylFrequency b h r m| := by
  have hpowNat : 2 ^ (r - 1) ≤ b ^ r - b ^ m :=
    two_pow_le_pow_sub_pow hb hm hmr
  have hpow :
      (2 : ℝ) ^ (r - 1) ≤ (b : ℝ) ^ r - (b : ℝ) ^ m := by
    exact_mod_cast hpowNat
  have hdiff :
      0 ≤ (b : ℝ) ^ r - (b : ℝ) ^ m :=
    le_trans (pow_nonneg (by positivity) _) hpow
  have hhabs : (1 : ℝ) ≤ |(h : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
    exact Int.one_le_abs hh
  rw [weylFrequency, abs_mul, abs_of_nonneg hdiff]
  exact hpow.trans (by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hhabs hdiff)

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
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro s hs
      exact integral_weylCorrelation b (r + 1) (s + 1) h
    · intro s hs
      exact integrable_weylCorrelation b (r + 1) (s + 1) h
  · intro r hr
    exact integrable_finset_sum _ fun s hs =>
      integrable_weylCorrelation b (r + 1) (s + 1) h

end TNumbersLean
