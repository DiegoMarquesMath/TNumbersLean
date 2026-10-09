import TNumbersLean.PaperBump
import TNumbersLean.PacketFourierTransform

namespace TNumbersLean

open MeasureTheory

/-- Complex-valued lift of the normalized real bump. -/
noncomputable def paperBumpComplex (x : ℝ) : ℂ :=
  (paperBump x : ℂ)

/-- Complex-valued version of one translated/rescaled packet bump. -/
noncomputable def complexPacketBumpTerm
    (q A : ℕ) (θ₀ : ℝ) (p : ℤ) (x : ℝ) : ℂ :=
  (packetBumpTerm paperBump q A θ₀ p x : ℂ)

/-- Exact Fourier transform of one translated and rescaled bump occurring in
the single-prime packet. -/
theorem packetFourier_complexPacketBumpTerm
    {q A : ℕ} (hq : 0 < q) (θ₀ : ℝ) (p : ℤ) (t : ℝ) :
    packetFourier (complexPacketBumpTerm q A θ₀ p) t =
      Real.fourierChar (-(θ₀ + (p : ℝ) / (q : ℝ)) * t) •
        ((((q : ℝ) ^ A)⁻¹) •
          packetFourier paperBumpComplex (t / ((q : ℝ) ^ A))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  have hscale : (0 : ℝ) < (q : ℝ) ^ A := pow_pos hqR A
  have h :=
    packetFourier_affine_pos
      paperBumpComplex hscale
      (θ₀ + (p : ℝ) / (q : ℝ)) t
  simpa [complexPacketBumpTerm, paperBumpComplex, packetBumpTerm,
    sub_eq_add_neg, add_assoc] using h

/-- The scale factor cancels the Jacobian in the manuscript normalization. -/
theorem packetFourier_scaled_complexPacketBumpTerm
    {q A : ℕ} (hq : 0 < q) (θ₀ : ℝ) (p : ℤ) (t : ℝ) :
    ((q : ℝ) ^ A : ℂ) •
        packetFourier (complexPacketBumpTerm q A θ₀ p) t =
      Real.fourierChar (-(θ₀ + (p : ℝ) / (q : ℝ)) * t) •
        packetFourier paperBumpComplex (t / ((q : ℝ) ^ A)) := by
  rw [packetFourier_complexPacketBumpTerm hq θ₀ p t]
  have hqR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  have hscale : ((q : ℝ) ^ A) ≠ 0 := (pow_pos hqR A).ne'
  rw [smul_smul, smul_smul]
  congr 1
  norm_cast
  field_simp [hscale]

end TNumbersLean
