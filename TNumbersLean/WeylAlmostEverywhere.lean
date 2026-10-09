import TNumbersLean.FourierBorelCantelli
import TNumbersLean.WeylInterpolation

namespace TNumbersLean

open Filter MeasureTheory
open scoped Topology

/-- For a fixed base and nonzero Fourier frequency, the paper's Fourier
decay implies almost-sure convergence of the normalized Weyl sums. -/
theorem ae_normalizedWeylSum_tendsto_zero_of_fourierDecay
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c)
    {b : ℕ} (hb : 2 ≤ b) {h : ℤ} (hh : h ≠ 0) :
    ∀ᵐ x ∂μ,
      Tendsto
        (fun N : ℕ => normalizedWeylSum b h x N)
        atTop (𝓝 0) := by
  filter_upwards
    [ae_squareNormRatio_weyl_tendsto_zero hdecay hb hh]
    with x hx
  exact normalizedWeylSum_tendsto_zero_of_squareNormRatio b h x hx

/-- Countable intersection over all nonzero integer frequencies gives
Weyl normality to a fixed base almost everywhere. -/
theorem ae_weylNormalToBase_of_fourierDecay
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c)
    {b : ℕ} (hb : 2 ≤ b) :
    ∀ᵐ x ∂μ, WeylNormalToBase b x := by
  have hall :
      ∀ᵐ x ∂μ, ∀ h : ℤ, h ≠ 0 →
        Tendsto
          (fun N : ℕ => normalizedWeylSum b h x N)
          atTop (𝓝 0) := by
    apply ae_all_iff.2
    intro h
    by_cases hh : h = 0
    · exact ae_of_all μ fun _ hne => (hne hh).elim
    · filter_upwards
        [ae_normalizedWeylSum_tendsto_zero_of_fourierDecay
          hdecay hb hh]
        with x hx
      intro _
      exact hx
  filter_upwards [hall] with x hx
  exact weylNormalToBase_of_all_frequencies hx

/-- Countable intersection over all integer bases b >= 2 gives simultaneous
Weyl normality to every base almost everywhere. -/
theorem ae_weylAbsolutelyNormal_of_fourierDecay
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c) :
    ∀ᵐ x ∂μ, WeylAbsolutelyNormal x := by
  have hall :
      ∀ᵐ x ∂μ, ∀ b : ℕ, 2 ≤ b → WeylNormalToBase b x := by
    apply ae_all_iff.2
    intro b
    by_cases hb : 2 ≤ b
    · filter_upwards
        [ae_weylNormalToBase_of_fourierDecay hdecay hb]
        with x hx
      intro _
      exact hx
    · exact ae_of_all μ fun _ hb' => (hb hb').elim
  filter_upwards [hall] with x hx
  exact weylAbsolutelyNormal_of_all_bases hx

end TNumbersLean
