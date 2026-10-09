import Mathlib.Analysis.Calculus.BumpFunction.Normed
import TNumbersLean.PacketBumpGeometry

namespace TNumbersLean

open MeasureTheory Set

/-- A concrete smooth bump centered at zero, with inner radius `1/8` and
outer radius `1/4`. -/
noncomputable def paperContDiffBump : ContDiffBump (0 : ℝ) :=
  ⟨(1 / 8 : ℝ), (1 / 4 : ℝ), by norm_num, by norm_num⟩

/-- The normalized bump used in the packet construction.  Mathlib's
normalization gives integral one automatically. -/
noncomputable def paperBump : ℝ → ℝ :=
  paperContDiffBump.normed volume

theorem paperBump_nonneg (x : ℝ) :
    0 ≤ paperBump x := by
  exact paperContDiffBump.nonneg_normed (μ := volume) x

theorem paperBump_contDiff :
    ContDiff ℝ ∞ paperBump := by
  exact paperContDiffBump.contDiff_normed (μ := volume)

theorem paperBump_integrable :
    Integrable paperBump := by
  exact paperContDiffBump.integrable_normed (μ := volume)

theorem integral_paperBump :
    (∫ x : ℝ, paperBump x) = 1 := by
  exact paperContDiffBump.integral_normed (μ := volume)

theorem support_paperBump_eq :
    Function.support paperBump = Set.Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ) := by
  rw [paperBump, paperContDiffBump.support_normed_eq, Real.ball_eq_Ioo]
  simp [paperContDiffBump]
  norm_num

theorem support_paperBump_subset :
    Function.support paperBump ⊆ Set.Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ) := by
  rw [support_paperBump_eq]

end TNumbersLean
