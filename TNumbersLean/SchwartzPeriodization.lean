import Mathlib.Analysis.Fourier.PoissonSummation

namespace TNumbersLean

open Function Set TopologicalSpace Filter MeasureTheory Asymptotics ContinuousMap
open scoped Real Filter FourierTransform

/-- Regard a Schwartz function as a bundled continuous map. -/
noncomputable def schwartzContinuousMap (f : SchwartzMap ℝ ℂ) : C(ℝ, ℂ) :=
  ⟨f, f.continuous⟩

/-- The translates of a Schwartz function are locally summable in the uniform
norm on every compact set.  This packages the convergence hypothesis required
by mathlib's periodization/Fourier-coefficient theorem. -/
theorem schwartz_periodization_local_summable (f : SchwartzMap ℝ ℂ) :
    ∀ K : Compacts ℝ,
      Summable fun n : ℤ =>
        ‖((schwartzContinuousMap f).comp (ContinuousMap.addRight n)).restrict K‖ := by
  intro K
  have hfO :
      (schwartzContinuousMap f : ℝ → ℂ) =O[cocompact ℝ]
        (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
    simpa [schwartzContinuousMap, Real.norm_eq_abs] using
      f.isBigO_cocompact_rpow (-2)
  exact
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((isBigO_norm_restrict_cocompact
          (schwartzContinuousMap f) (by norm_num : (0 : ℝ) < 2) hfO K).comp_tendsto
        Int.tendsto_coe_cofinite)

/-- For a Schwartz function, the Fourier coefficient of its periodization is
its ordinary Fourier transform at the corresponding integer frequency. -/
theorem fourierCoeff_periodization_schwartz
    (f : SchwartzMap ℝ ℂ) (m : ℤ) :
    fourierCoeff
        (Periodic.lift <|
          (schwartzContinuousMap f).periodic_tsum_comp_add_zsmul 1) m =
      𝓕 (schwartzContinuousMap f) m := by
  exact Real.fourierCoeff_tsum_comp_add
    (schwartz_periodization_local_summable f) m

end TNumbersLean
