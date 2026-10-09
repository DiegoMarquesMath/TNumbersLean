import Mathlib.Analysis.Distribution.FourierSchwartz
import TNumbersLean.PacketBumpSchwartz

namespace TNumbersLean

open MeasureTheory
open scoped FourierTransform

/-- The Fourier transform of the normalized paper bump, bundled again as a
Schwartz function. -/
noncomputable def paperBumpFourierSchwartz : SchwartzMap ℝ ℂ :=
  SchwartzMap.fourierTransformCLM ℝ paperBumpSchwartz

/-- The bundled Schwartz Fourier transform agrees pointwise with the packet
Fourier convention used throughout the manuscript formalization. -/
theorem paperBumpFourierSchwartz_apply (u : ℝ) :
    paperBumpFourierSchwartz u =
      packetFourier paperBumpComplex u := by
  rw [paperBumpFourierSchwartz, SchwartzMap.fourierTransformCLM_apply]
  rw [Real.fourierIntegral_real_eq]
  rw [packetFourier_def]
  apply integral_congr_ae
  filter_upwards with x
  rw [paperBumpSchwartz_apply]

/-- A fixed Schwartz seminorm constant controlling the quadratic decay of the
Fourier transform of the paper bump. -/
noncomputable def paperBumpFourierDecayConstant : ℝ :=
  (2 : ℝ) ^ 2 *
    (Finset.Iic (2, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2)
      paperBumpFourierSchwartz

/-- Global quadratic decay in a denominator-free form. -/
theorem paperBumpFourier_weighted_decay (u : ℝ) :
    (1 + |u|) ^ 2 *
        ‖packetFourier paperBumpComplex u‖ ≤
      paperBumpFourierDecayConstant := by
  have h :=
    SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (E := ℝ) (F := ℂ)
      (m := (2, 0)) (k := 2) (n := 0)
      (by simp) (by simp)
      paperBumpFourierSchwartz u
  simp only [norm_iteratedFDeriv_zero] at h
  rw [paperBumpFourierSchwartz_apply] at h
  simpa [paperBumpFourierDecayConstant, Real.norm_eq_abs] using h

theorem paperBumpFourierDecayConstant_nonneg :
    0 ≤ paperBumpFourierDecayConstant := by
  have h := paperBumpFourier_weighted_decay 0
  have hnorm :
      0 ≤ ‖packetFourier paperBumpComplex 0‖ := norm_nonneg _
  have hle :
      ‖packetFourier paperBumpComplex 0‖ ≤
        paperBumpFourierDecayConstant := by
    simpa using h
  exact hnorm.trans hle

/-- The familiar manuscript form
`|hat phi(u)| <= C_phi (1+|u|)^(-2)`. -/
theorem norm_packetFourier_paperBump_le (u : ℝ) :
    ‖packetFourier paperBumpComplex u‖ ≤
      paperBumpFourierDecayConstant / (1 + |u|) ^ 2 := by
  have hden : 0 < (1 + |u|) ^ 2 := by positivity
  apply (le_div_iff₀ hden).2
  simpa [mul_comm] using paperBumpFourier_weighted_decay u

end TNumbersLean
