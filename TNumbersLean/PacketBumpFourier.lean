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

theorem complexPacketBumpTerm_eq_affine
    (q A : ℕ) (θ₀ : ℝ) (p : ℤ) (x : ℝ) :
    complexPacketBumpTerm q A θ₀ p x =
      paperBumpComplex
        (((q : ℝ) ^ A) * (x - (θ₀ + (p : ℝ) / (q : ℝ)))) := by
  simp only [complexPacketBumpTerm, packetBumpTerm, paperBumpComplex]
  norm_cast
  congr 1
  ring

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
  rw [show complexPacketBumpTerm q A θ₀ p =
      fun x => paperBumpComplex
        (((q : ℝ) ^ A) * (x - (θ₀ + (p : ℝ) / (q : ℝ)))) by
        funext x
        exact complexPacketBumpTerm_eq_affine q A θ₀ p x]
  exact
    packetFourier_affine_pos
      paperBumpComplex hscale
      (θ₀ + (p : ℝ) / (q : ℝ)) t

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
  simp only [Circle.smul_def, Complex.real_smul, smul_eq_mul]
  push_cast
  field_simp [hscale]

end TNumbersLean
