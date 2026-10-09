import TNumbersLean.FourierTailSummability

namespace TNumbersLean

open Filter Finset MeasureTheory
open scoped BigOperators Topology

/-- The squared norm of a finite Weyl sum is integrable against every
finite measure. -/
theorem integrable_normSq_weylSum
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (b N : ℕ) (h : ℤ) :
    Integrable (fun x : ℝ => ‖weylSum b h x N‖ ^ 2) μ := by
  refine Integrable.of_bound ?_ ((N : ℝ) ^ 2) ?_
  · apply Continuous.aestronglyMeasurable
    unfold weylSum weylTerm circleExp
    fun_prop
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact
      (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg N)).2
        (norm_weylSum_le b h x N)

/-- Chebyshev's inequality plus the linear second-moment estimate gives
the summable j^{-2} majorant for the bad sets on square indices. -/
theorem measureReal_squareBadSet_weyl_le_inv_sq
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c)
    {b : ℕ} (hb : 2 ≤ b) {h : ℤ} (hh : h ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    μ.real
        (squareBadSet
          (fun N x => weylSum b h x N) ε j) ≤
      ((1 + fourierOffDiagonalConstant C c) / ε ^ 2) *
        (1 / (j : ℝ) ^ 2) := by
  let K : ℝ := fourierOffDiagonalConstant C c
  have hK : 0 ≤ K := by
    dsimp [K]
    exact fourierOffDiagonalConstant_nonneg hdecay.1.le
  by_cases hj : j = 0
  · subst j
    simp [squareBadSet, weylSum]
  have hjNat : 0 < j := Nat.pos_of_ne_zero hj
  have hjr : (0 : ℝ) < j := by
    exact_mod_cast hjNat
  have hj2pos : (0 : ℝ) < (j : ℝ) ^ 2 := sq_pos_of_pos hjr
  have hthreshold :
      0 < (ε * (j : ℝ) ^ 2) ^ 2 := by
    positivity
  have hsubset :
      squareBadSet (fun N x => weylSum b h x N) ε j ⊆
        {x : ℝ |
          (ε * (j : ℝ) ^ 2) ^ 2 ≤
            ‖weylSum b h x (j ^ 2)‖ ^ 2} := by
    intro x hx
    change ε * (j : ℝ) ^ 2 < ‖weylSum b h x (j ^ 2)‖ at hx
    exact
      (sq_le_sq₀ (mul_nonneg hε.le (sq_nonneg _)) (norm_nonneg _)).2
        hx.le
  have hmarkov :
      (ε * (j : ℝ) ^ 2) ^ 2 *
          μ.real
            {x : ℝ |
              (ε * (j : ℝ) ^ 2) ^ 2 ≤
                ‖weylSum b h x (j ^ 2)‖ ^ 2} ≤
        weylSecondMoment μ b h (j ^ 2) := by
    simpa [weylSecondMoment] using
      (MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (μ := μ)
        (f := fun x : ℝ => ‖weylSum b h x (j ^ 2)‖ ^ 2)
        (ae_of_all μ fun x => sq_nonneg ‖weylSum b h x (j ^ 2)‖)
        (integrable_normSq_weylSum (μ := μ) b (j ^ 2) h)
        ((ε * (j : ℝ) ^ 2) ^ 2))
  have hbad_markov :
      (ε * (j : ℝ) ^ 2) ^ 2 *
          μ.real
            (squareBadSet
              (fun N x => weylSum b h x N) ε j) ≤
        weylSecondMoment μ b h (j ^ 2) := by
    exact
      (mul_le_mul_of_nonneg_left
        (measureReal_mono hsubset) hthreshold.le).trans hmarkov
  have hmom :
      weylSecondMoment μ b h (j ^ 2) ≤
        ((j ^ 2 : ℕ) : ℝ) + K := by
    dsimp [K]
    exact weylSecondMoment_le_linear hdecay hb hh (j ^ 2)
  have hmul :
      (ε * (j : ℝ) ^ 2) ^ 2 *
          μ.real
            (squareBadSet
              (fun N x => weylSum b h x N) ε j) ≤
        ((j ^ 2 : ℕ) : ℝ) + K :=
    hbad_markov.trans hmom
  have hdiv :
      μ.real
          (squareBadSet
            (fun N x => weylSum b h x N) ε j) ≤
        (((j ^ 2 : ℕ) : ℝ) + K) /
          (ε * (j : ℝ) ^ 2) ^ 2 := by
    rw [le_div_iff₀ hthreshold]
    simpa [mul_comm] using hmul
  have hjone : (1 : ℝ) ≤ j := by
    exact_mod_cast hjNat
  have hj2one : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
    nlinarith
  have hKle :
      K ≤ K * (j : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hj2one)]
  have hnum :
      (j : ℝ) ^ 2 + K ≤
        (1 + K) * (j : ℝ) ^ 2 := by
    nlinarith
  have hcoarse :
      ((j : ℝ) ^ 2 + K) /
          (ε * (j : ℝ) ^ 2) ^ 2 ≤
        ((1 + K) / ε ^ 2) *
          (1 / (j : ℝ) ^ 2) := by
    calc
      ((j : ℝ) ^ 2 + K) /
            (ε * (j : ℝ) ^ 2) ^ 2
          ≤ ((1 + K) * (j : ℝ) ^ 2) /
              (ε * (j : ℝ) ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ =
          ((1 + K) / ε ^ 2) *
            (1 / (j : ℝ) ^ 2) := by
        field_simp [ne_of_gt hε, ne_of_gt hjr]
  calc
    μ.real
        (squareBadSet
          (fun N x => weylSum b h x N) ε j)
        ≤ (((j ^ 2 : ℕ) : ℝ) + K) /
            (ε * (j : ℝ) ^ 2) ^ 2 := hdiv
    _ = ((j : ℝ) ^ 2 + K) /
          (ε * (j : ℝ) ^ 2) ^ 2 := by
      norm_cast
    _ ≤ ((1 + K) / ε ^ 2) *
          (1 / (j : ℝ) ^ 2) := hcoarse
    _ =
        ((1 + fourierOffDiagonalConstant C c) / ε ^ 2) *
          (1 / (j : ℝ) ^ 2) := by
      rfl

/-- The real measures of the square-subsequence bad sets are summable. -/
theorem summable_measureReal_squareBadSet_weyl
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c)
    {b : ℕ} (hb : 2 ≤ b) {h : ℤ} (hh : h ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    Summable
      (fun j : ℕ =>
        μ.real
          (squareBadSet
            (fun N x => weylSum b h x N) ε j)) := by
  let D : ℝ :=
    (1 + fourierOffDiagonalConstant C c) / ε ^ 2
  have hbase :
      Summable (fun j : ℕ => D * (1 / (j : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr
      (by norm_num : (1 : ℕ) < 2)).mul_left D
  refine Summable.of_nonneg_of_le
    (fun j => measureReal_nonneg) ?_ hbase
  intro j
  simpa [D] using
    (measureReal_squareBadSet_weyl_le_inv_sq
      hdecay hb hh hε j)

/-- For a finite measure, summability of the real-valued measures is
equivalent to the ENNReal finiteness needed by first Borel--Cantelli. -/
theorem tsum_measure_ne_top_of_summable_measureReal
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ]
    {A : ℕ → Set α}
    (hsum : Summable (fun n : ℕ => μ.real (A n))) :
    (∑' n : ℕ, μ (A n)) ≠ ⊤ := by
  let f : ℕ → NNReal := fun n => (μ (A n)).toNNReal
  have hreal :
      Summable (fun n : ℕ => (f n : ℝ)) := by
    simpa only [f, measureReal_def, ENNReal.coe_toNNReal_eq_toReal] using hsum
  have htop :
      (∑' n : ℕ, (f n : ENNReal)) ≠ ⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.2 hreal
  have hfun :
      (fun n : ℕ => (f n : ENNReal)) =
        (fun n : ℕ => μ (A n)) := by
    funext n
    dsimp [f]
    exact ENNReal.coe_toNNReal (measure_ne_top μ (A n))
  rw [hfun] at htop
  exact htop

/-- ENNReal summability of the Weyl bad sets, in the exact form required
by the Borel--Cantelli lemma already formalized earlier. -/
theorem tsum_squareBadSet_weyl_ne_top
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c)
    {b : ℕ} (hb : 2 ≤ b) {h : ℤ} (hh : h ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    (∑' j : ℕ,
      μ
        (squareBadSet
          (fun N x => weylSum b h x N) ε j)) ≠ ⊤ := by
  apply tsum_measure_ne_top_of_summable_measureReal
  exact summable_measureReal_squareBadSet_weyl
    hdecay hb hh hε

/-- Under the paper's Fourier-decay hypothesis, the Weyl sums along
square indices are almost surely o(j^2). -/
theorem ae_squareNormRatio_weyl_tendsto_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c)
    {b : ℕ} (hb : 2 ≤ b) {h : ℤ} (hh : h ≠ 0) :
    ∀ᵐ x ∂μ,
      Tendsto
        (squareNormRatio
          (fun N y => weylSum b h y N) x)
        atTop (𝓝 0) := by
  apply ae_squareNormRatio_tendsto_zero_of_summable_bad
  intro m hm
  have hmreal : (0 : ℝ) < m := by
    exact_mod_cast hm
  exact tsum_squareBadSet_weyl_ne_top
    hdecay hb hh (inv_pos.mpr hmreal)

end TNumbersLean
