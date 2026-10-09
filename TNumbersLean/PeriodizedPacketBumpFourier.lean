import TNumbersLean.PacketBumpSchwartz

namespace TNumbersLean

open Function Set TopologicalSpace MeasureTheory ContinuousMap
open scoped FourierTransform

/-- Periodization modulo one of a single affine packet bump. -/
noncomputable def periodizedAffinePacketBump
    {q A : ℕ} (hq : 0 < q) (θ₀ : ℝ) (p : ℤ) :
    UnitAddCircle → ℂ :=
  Periodic.lift <|
    ContinuousMap.periodic_tsum_comp_add_zsmul
      (schwartzContinuousMap
        (affinePacketBumpSchwartz (A := A) hq θ₀ p)) 1

/-- The Fourier coefficient of the periodized affine bump is its ordinary
Fourier transform at the corresponding integer frequency. -/
theorem fourierCoeff_periodizedAffinePacketBump
    {q A : ℕ} (hq : 0 < q) (θ₀ : ℝ) (p : ℤ) (ell : ℤ) :
    fourierCoeff
        (periodizedAffinePacketBump (A := A) hq θ₀ p) ell =
      packetFourier (complexPacketBumpTerm q A θ₀ p) (ell : ℝ) := by
  have h :=
    fourierCoeff_periodization_schwartz
      (affinePacketBumpSchwartz (A := A) hq θ₀ p) ell
  have hfun :
      (schwartzContinuousMap
          (affinePacketBumpSchwartz (A := A) hq θ₀ p) : ℝ → ℂ) =
        complexPacketBumpTerm q A θ₀ p := by
    funext x
    rw [show
      (schwartzContinuousMap
        (affinePacketBumpSchwartz (A := A) hq θ₀ p) : ℝ → ℂ) x =
          affinePacketBumpComplex q A θ₀ p x by rfl]
    exact congrFun (affinePacketBumpComplex_eq q A θ₀ p) x
  rw [hfun] at h
  simpa [periodizedAffinePacketBump, packetFourier] using h

/-- Fully explicit coefficient formula for one periodized affine bump. -/
theorem fourierCoeff_periodizedAffinePacketBump_eq
    {q A : ℕ} (hq : 0 < q) (θ₀ : ℝ) (p : ℤ) (ell : ℤ) :
    fourierCoeff
        (periodizedAffinePacketBump (A := A) hq θ₀ p) ell =
      Real.fourierChar
          (-(θ₀ + (p : ℝ) / (q : ℝ)) * (ell : ℝ)) •
        ((((q : ℝ) ^ A)⁻¹) •
          packetFourier paperBumpComplex
            ((ell : ℝ) / ((q : ℝ) ^ A))) := by
  rw [fourierCoeff_periodizedAffinePacketBump
    (A := A) hq θ₀ p ell]
  exact packetFourier_complexPacketBumpTerm hq θ₀ p (ell : ℝ)

end TNumbersLean
