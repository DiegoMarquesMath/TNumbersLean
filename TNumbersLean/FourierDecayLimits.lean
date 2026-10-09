import TNumbersLean.FourierSecondMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace TNumbersLean

open Filter
open scoped Topology

/-- The stretched-logarithmic profile occurring in the manuscript tends to zero
at positive infinity. -/
theorem tendsto_paperDecayProfile_atTop
    {c : ℝ} (hc : 0 < c) :
    Tendsto (paperDecayProfile c) atTop (𝓝 0) := by
  have hshift : Tendsto (fun t : ℝ => t + 2) atTop atTop := by
    apply tendsto_atTop_add_const_right
    exact tendsto_id
  have hlog : Tendsto (fun t : ℝ => Real.log (t + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp hshift
  have hpow :
      Tendsto (fun t : ℝ => (Real.log (t + 2)) ^ ((1 : ℝ) / 4)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)).comp hlog
  have hneg :
      Tendsto (fun t : ℝ => -c * (Real.log (t + 2)) ^ ((1 : ℝ) / 4)) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hc)).2 hpow
  have hexp :
      Tendsto
        (fun t : ℝ => Real.exp (-c * (Real.log (t + 2)) ^ ((1 : ℝ) / 4)))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [paperDecayProfile, abs_of_nonneg ht, add_comm]

/-- The manuscript's Fourier-decay hypothesis in particular forces the norm of
the Fourier transform to vanish at positive infinity. -/
theorem tendsto_norm_paperFourier_atTop_of_decay
    {μ : MeasureTheory.Measure ℝ} {C c : ℝ}
    (hdecay : HasPaperFourierDecay μ C c) :
    Tendsto (fun t : ℝ => ‖paperFourier μ t‖) atTop (𝓝 0) := by
  rcases hdecay with ⟨hC, hc, hbound⟩
  apply squeeze_zero
  · intro t
    exact norm_nonneg _
  · exact hbound
  · simpa using
      (tendsto_const_nhds.mul (tendsto_paperDecayProfile_atTop (c := c) hc))


/-- In the characteristic-function convention used by mathlib, the same decay
implies vanishing at positive infinity. -/
theorem tendsto_norm_charFun_atTop_of_paperDecay
    {μ : MeasureTheory.Measure ℝ} {C c : ℝ}
    (hdecay : HasPaperFourierDecay μ C c) :
    Tendsto (fun t : ℝ => ‖MeasureTheory.charFun μ t‖) atTop (𝓝 0) := by
  have hscale :
      Tendsto (fun t : ℝ => t / (2 * Real.pi)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have hcomp :=
    (tendsto_norm_paperFourier_atTop_of_decay hdecay).comp hscale
  refine hcomp.congr' ?_
  filter_upwards with t
  have harg : 2 * Real.pi * (t / (2 * Real.pi)) = t := by
    field_simp [Real.pi_ne_zero]
  simp [paperFourier, harg]

end TNumbersLean
