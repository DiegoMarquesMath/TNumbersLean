import Mathlib.Analysis.SpecificLimits.Basic

namespace TNumbersLean

open Finset

/-- The stagewise mass-error budget corresponding to the manuscript bound
`2^(-k-4)` for stages `k ≥ 1`, reindexed by `n = k - 1`. -/
noncomputable def measureMassIncrementBudget (n : ℕ) : ℝ :=
  (1 / 16 : ℝ) / 2 / 2 ^ n

theorem measureMassIncrementBudget_nonneg (n : ℕ) :
    0 ≤ measureMassIncrementBudget n := by
  unfold measureMassIncrementBudget
  positivity

/-- The total mass perturbation allowed by the Fourier increments is exactly
`1/16`. -/
theorem hasSum_measureMassIncrementBudget :
    HasSum measureMassIncrementBudget (1 / 16 : ℝ) := by
  change HasSum (fun n : ℕ => (1 / 16 : ℝ) / 2 / 2 ^ n) (1 / 16 : ℝ)
  exact hasSum_geometric_two' (1 / 16 : ℝ)

theorem summable_measureMassIncrementBudget :
    Summable measureMassIncrementBudget :=
  hasSum_measureMassIncrementBudget.summable

theorem tsum_measureMassIncrementBudget :
    ∑' n : ℕ, measureMassIncrementBudget n = (1 / 16 : ℝ) :=
  hasSum_measureMassIncrementBudget.tsum_eq

/-- Any sequence starting at mass one and changing at stage `n` by at most
the prescribed budget stays within total distance `1/16` of one. -/
theorem abs_mass_sub_one_le_one_sixteenth
    (m : ℕ → ℝ)
    (h0 : m 0 = 1)
    (hstep : ∀ n, |m (n + 1) - m n| ≤ measureMassIncrementBudget n) :
    ∀ n, |m n - 1| ≤ (1 / 16 : ℝ) := by
  have hpartial : ∀ n, |m n - 1| ≤ ∑ i ∈ range n, measureMassIncrementBudget i := by
    intro n
    induction n with
    | zero =>
        simp [h0]
    | succ n ih =>
        calc
          |m (n + 1) - 1|
              = |(m (n + 1) - m n) + (m n - 1)| := by ring_nf
          _ ≤ |m (n + 1) - m n| + |m n - 1| := abs_add _ _
          _ ≤ measureMassIncrementBudget n +
                ∑ i ∈ range n, measureMassIncrementBudget i :=
              add_le_add (hstep n) ih
          _ = ∑ i ∈ range (n + 1), measureMassIncrementBudget i := by
              rw [sum_range_succ]
              exact add_comm _ _
  intro n
  calc
    |m n - 1| ≤ ∑ i ∈ range n, measureMassIncrementBudget i := hpartial n
    _ ≤ ∑' i : ℕ, measureMassIncrementBudget i :=
      summable_measureMassIncrementBudget.sum_le_tsum
        (range n) (fun i _ => measureMassIncrementBudget_nonneg i)
    _ = (1 / 16 : ℝ) := tsum_measureMassIncrementBudget

/-- Consequently every finite-stage mass lies in the interval appearing in the
manuscript, `[15/16, 17/16]`. -/
theorem mass_mem_Icc_fifteen_sixteen_seventeen_sixteen
    (m : ℕ → ℝ)
    (h0 : m 0 = 1)
    (hstep : ∀ n, |m (n + 1) - m n| ≤ measureMassIncrementBudget n)
    (n : ℕ) :
    (15 / 16 : ℝ) ≤ m n ∧ m n ≤ (17 / 16 : ℝ) := by
  have h := abs_mass_sub_one_le_one_sixteenth m h0 hstep n
  rw [abs_le] at h
  constructor <;> linarith

end TNumbersLean
