import TNumbersLean.NormalityFromFourier
import TNumbersLean.DoubleSumTriangle
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
  have hbase : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
  have hpowOrder : b ^ m ≤ b ^ r :=
    pow_le_pow_right' hbase hmr.le
  have hpowCast :
      ((2 ^ (r - 1) : ℕ) : ℝ) ≤ ((b ^ r - b ^ m : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  have hpow :
      (2 : ℝ) ^ (r - 1) ≤ (b : ℝ) ^ r - (b : ℝ) ^ m := by
    simpa [Nat.cast_sub hpowOrder] using hpowCast
  have hdiff :
      0 ≤ (b : ℝ) ^ r - (b : ℝ) ^ m :=
    le_trans (pow_nonneg (by positivity) _) hpow
  have hhabs : (1 : ℝ) ≤ |(h : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
    exact Int.one_le_abs hh
  rw [weylFrequency, abs_mul, abs_of_nonneg hdiff]
  exact hpow.trans (by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hhabs hdiff)


/-- The stretched-logarithmic decay profile in equation (1.4) of the manuscript. -/
noncomputable def paperDecayProfile (c t : ℝ) : ℝ :=
  Real.exp (-c * (Real.log (2 + |t|)) ^ ((1 : ℝ) / 4))

/-- Literal formulation of the Fourier-decay hypothesis used in Section 6. -/
def HasPaperFourierDecay (μ : Measure ℝ) (C c : ℝ) : Prop :=
  0 < C ∧ 0 < c ∧
    ∀ t : ℝ, ‖paperFourier μ t‖ ≤ C * paperDecayProfile c t

theorem paperDecayProfile_le_of_abs_ge
    {c u t : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) (hut : u ≤ |t|) :
    paperDecayProfile c t ≤
      Real.exp (-c * (Real.log (2 + u)) ^ ((1 : ℝ) / 4)) := by
  unfold paperDecayProfile
  apply Real.exp_le_exp.mpr
  have hlog :
      Real.log (2 + u) ≤ Real.log (2 + |t|) := by
    apply Real.log_le_log
    · linarith
    · linarith
  have hlog_nonneg : 0 ≤ Real.log (2 + u) := by
    exact Real.log_nonneg (by linarith)
  have hroot :
      (Real.log (2 + u)) ^ ((1 : ℝ) / 4) ≤
        (Real.log (2 + |t|)) ^ ((1 : ℝ) / 4) := by
    exact Real.rpow_le_rpow hlog_nonneg hlog (by norm_num)
  exact mul_le_mul_of_nonpos_left hroot (neg_nonpos.mpr hc)

/-- Fourier decay at an off-diagonal Weyl frequency, with the frequency
replaced by the paper's lacunary lower bound 2^(r-1). -/
theorem paperFourier_offdiag_decay
    {μ : Measure ℝ} {C c : ℝ}
    (hdecay : HasPaperFourierDecay μ C c)
    {b m r : ℕ} {h : ℤ}
    (hb : 2 ≤ b) (hh : h ≠ 0) (hm : 1 ≤ m) (hmr : m < r) :
    ‖paperFourier μ (weylFrequency b h r m)‖ ≤
      C * Real.exp
        (-c * (Real.log (2 + (2 : ℝ) ^ (r - 1))) ^ ((1 : ℝ) / 4)) := by
  rcases hdecay with ⟨hC, hc, hbound⟩
  refine (hbound (weylFrequency b h r m)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact paperDecayProfile_le_of_abs_ge hc.le (by positivity)
    (abs_weylFrequency_lower_bound hb hh hm hmr)


theorem paperFourier_decay_of_abs_ge
    {μ : Measure ℝ} {C c u t : ℝ}
    (hdecay : HasPaperFourierDecay μ C c)
    (hu : 0 ≤ u) (hut : u ≤ |t|) :
    ‖paperFourier μ t‖ ≤
      C * Real.exp
        (-c * (Real.log (2 + u)) ^ ((1 : ℝ) / 4)) := by
  rcases hdecay with ⟨hC, hc, hbound⟩
  refine (hbound t).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact paperDecayProfile_le_of_abs_ge hc.le hu hut

theorem abs_weylFrequency_swap
    (b r s : ℕ) (h : ℤ) :
    |weylFrequency b h r s| = |weylFrequency b h s r| := by
  have hneg :
      weylFrequency b h r s = -weylFrequency b h s r := by
    simp only [weylFrequency]
    ring
  rw [hneg, abs_neg]

/-- Finite second-moment bound obtained directly from the Fourier-decay
hypothesis and lacunarity.  This is the finite-sum form of (6.1), before
replacing the off-diagonal sum by an absolute constant. -/
theorem weylSecondMoment_le_decay_triangle
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c)
    {b : ℕ} (hb : 2 ≤ b) {h : ℤ} (hh : h ≠ 0) (N : ℕ) :
    weylSecondMoment μ b h N ≤
      (N : ℝ) +
        2 * ∑ r ∈ Finset.range N,
          (r : ℝ) *
            (C * Real.exp
              (-c * (Real.log (2 + (2 : ℝ) ^ r)) ^ ((1 : ℝ) / 4))) := by
  refine (weylSecondMoment_le_doubleNormSum (μ := μ) b N h).trans ?_
  apply double_sum_le_diag_add_two_triangle
  · intro r
    simp
  · intro s r hsr
    have hfreq :
        (2 : ℝ) ^ r ≤
          |weylFrequency b h (r + 1) (s + 1)| := by
      simpa using
        (abs_weylFrequency_lower_bound
          (b := b) (h := h) (m := s + 1) (r := r + 1)
          hb hh (by omega) (by omega))
    exact paperFourier_decay_of_abs_ge hdecay (by positivity) hfreq
  · intro r s hrs
    have hrev :
        (2 : ℝ) ^ s ≤
          |weylFrequency b h (s + 1) (r + 1)| := by
      simpa using
        (abs_weylFrequency_lower_bound
          (b := b) (h := h) (m := r + 1) (r := s + 1)
          hb hh (by omega) (by omega))
    have hfreq :
        (2 : ℝ) ^ s ≤
          |weylFrequency b h (r + 1) (s + 1)| := by
      rw [abs_weylFrequency_swap]
      exact hrev
    exact paperFourier_decay_of_abs_ge hdecay (by positivity) hfreq

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

/-- The real second moment appearing in (6.1). -/
noncomputable def weylSecondMoment
    (μ : Measure ℝ) (b : ℕ) (h : ℤ) (N : ℕ) : ℝ :=
  ∫ x : ℝ, ‖weylSum b h x N‖ ^ 2 ∂μ

/-- Real form of the exact finite correlation identity. -/
theorem weylSecondMoment_eq_re_doubleFourier
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (b N : ℕ) (h : ℤ) :
    weylSecondMoment μ b h N =
      (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        paperFourier μ (weylFrequency b h (r + 1) (s + 1))).re := by
  have hcomplex :
      ((weylSecondMoment μ b h N : ℝ) : ℂ) =
        ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
          paperFourier μ (weylFrequency b h (r + 1) (s + 1)) := by
    rw [weylSecondMoment, ← integral_complex_ofReal]
    exact integral_normSq_weylSum_eq_doubleFourier (μ := μ) b N h
  have hcorr := congrArg Complex.re hcomplex
  simpa using hcorr

/-- Before using Fourier decay, the second moment is bounded by the sum
of the absolute values of all Fourier correlation terms. -/
theorem weylSecondMoment_le_doubleNormSum
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (b N : ℕ) (h : ℤ) :
    weylSecondMoment μ b h N ≤
      ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        ‖paperFourier μ (weylFrequency b h (r + 1) (s + 1))‖ := by
  rw [weylSecondMoment_eq_re_doubleFourier]
  calc
    (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        paperFourier μ (weylFrequency b h (r + 1) (s + 1))).re
        ≤ ‖∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
          paperFourier μ (weylFrequency b h (r + 1) (s + 1))‖ :=
      re_le_norm _
    _ ≤ ∑ r ∈ Finset.range N,
          ‖∑ s ∈ Finset.range N,
            paperFourier μ (weylFrequency b h (r + 1) (s + 1))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
          ‖paperFourier μ (weylFrequency b h (r + 1) (s + 1))‖ := by
      apply Finset.sum_le_sum
      intro r hr
      exact norm_sum_le _ _


end TNumbersLean
