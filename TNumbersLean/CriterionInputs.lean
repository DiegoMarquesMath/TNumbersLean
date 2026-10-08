import TNumbersLean.KoksmaExponent
import TNumbersLean.DiophantineBudget
import TNumbersLean.ScheduleBudget
import TNumbersLean.HeightOverlap

noncomputable section

namespace TNumbersLean

/-- Stage data and schedule properties of Lemma 3.1. These are construction
hypotheses, separate from the external algebraic inputs below. Stages are
indexed from zero (stage zero corresponds to manuscript stage one). -/
structure CriterionSchedule where
  Q : ℕ → ℝ
  d : ℕ → ℕ
  A : ℕ → ℕ
  scale_ge_four : ∀ k, 4 ≤ Q k
  degree_ge_two : ∀ k, 2 ≤ d k
  exponent_eq : ∀ k, A k = stageExponent (d k)
  scale_recurrence : ∀ k, Q (k + 1) = Q k ^ (100 * A k)
  scale_tends_to_infinity : Filter.Tendsto Q Filter.atTop Filter.atTop
  recurrent : ∀ d₀, 2 ≤ d₀ → {k | d k = d₀}.Infinite
  eventual_next_admissible : ∀ n, 1 ≤ n → ∃ k₀, ∀ k ≥ k₀,
    DegreeAdmissible d n (k + 1) ∨ DegreeAdmissible d n (k + 2)

/-- Witnesses for (3.7)--(3.8), and only the Section 2 algebraic inputs.
The denominator block is retained; (2.2) is supplied for the selected centers.
No global exclusion, transcendence, exponent bound, or T-number conclusion
is assumed. The separation field is Lemma 2.1 after the schedule's threshold
condition has been discharged. -/
structure CriterionInputs (S : AlgebraicApproximationSystem)
    (schedule : CriterionSchedule) (x : ℝ) where
  center : ℕ → ℝ
  q : ℕ → ℕ
  denominator_pos : ∀ k, 0 < q k
  denominator_lower : ∀ k, schedule.Q k ≤ (q k : ℝ)
  denominator_upper : ∀ k, (q k : ℝ) < 2 * schedule.Q k
  center_algebraic : ∀ k, S.isAlg (center k)
  center_exact_degree : ∀ k, S.degree (center k) = schedule.d k
  source_approximation : ∀ k,
    |x - center k| ≤ (1 / 4 : ℝ) * (q k : ℝ) ^ (-(schedule.A k : ℝ))
  heightConstant : ℕ → ℝ
  heightConstant_ge_one : ∀ d, 2 ≤ d → 1 ≤ heightConstant d
  center_height_lower : ∀ k,
    (q k : ℝ) ^ schedule.d k ≤ S.height (center k)
  center_height_upper : ∀ k,
    S.height (center k) ≤ heightConstant (schedule.d k) * (q k : ℝ) ^ schedule.d k
  translated_center_separation : ∀ n k, 1 ≤ n → DegreeAdmissible schedule.d n k →
    ∀ β, S.isAlg β → S.degree β ≤ n →
      schedule.Q k ^ (-K (n : ℝ) - 1) * S.height β ^ (-(n : ℝ) - 2)
        ≤ |center k - β|

namespace CriterionInputs

variable {S : AlgebraicApproximationSystem} {s : CriterionSchedule} {x : ℝ}
    (I : CriterionInputs S s x)

/-- The Q-version of (3.8) used in (3.12), deduced from its q-version. -/
theorem source_approximation_Q (k : ℕ) :
    |x - I.center k| ≤ (1 / 4 : ℝ) * s.Q k ^ (-(s.A k : ℝ)) := by
  apply (I.source_approximation k).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_exponent_nonpos
    (by linarith [s.scale_ge_four k]) (I.denominator_lower k) (neg_nonpos.mpr (Nat.cast_nonneg _))

/-- The admissible cubic reserve uses the existing schedule exponent. -/
theorem admissible_exponent_lower (n k : ℕ) (h : DegreeAdmissible s.d n k) :
    (n + 2)^3 ≤ s.A k := by
  rw [s.exponent_eq]
  apply stageExponent_le_of_degree_le (n + 1) (s.d k)
  unfold DegreeAdmissible at h
  omega

/-- The reserve in (3.15), reusing the proved Diophantine budget. -/
theorem usable_exponent_lower (n k : ℕ) (h : DegreeAdmissible s.d n k) :
    (s.A k : ℝ) / (2 * ((n : ℝ) + 2)) ≤
      ((s.A k : ℝ) - K (n : ℝ) - 3) / ((n : ℝ) + 2) := by
  apply TNumbersLean.usable_exponent_lower _ _ (by positivity)
  exact_mod_cast admissible_exponent_lower n k h

end CriterionInputs
end TNumbersLean
