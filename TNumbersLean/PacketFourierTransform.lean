import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace TNumbersLean

open MeasureTheory

/-- Fourier transform of an integrable complex-valued function in the
manuscript convention `exp(-2*pi*i*t*x)`.  This is mathlib's real Fourier
integral with its standard character. -/
noncomputable def packetFourier (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  Fourier.fourierIntegral Real.fourierChar volume f t

theorem packetFourier_def (f : ℝ → ℂ) (t : ℝ) :
    packetFourier f t =
      ∫ x : ℝ, Real.fourierChar (-(x * t)) • f x := by
  rfl

/-- Translation rule in the manuscript Fourier convention. -/
theorem packetFourier_translate (f : ℝ → ℂ) (c t : ℝ) :
    packetFourier (fun x => f (x - c)) t =
      Real.fourierChar (-c * t) • packetFourier f t := by
  have h :=
    congrFun
      (Fourier.fourierIntegral_comp_add_right
        (E := ℂ) Real.fourierChar volume f (-c)) t
  simpa [packetFourier, Function.comp_def, sub_eq_add_neg] using h

/-- Scaling rule for the real Fourier transform.  The absolute Jacobian is
kept explicit, so the statement is valid for every nonzero real scale. -/
theorem packetFourier_scale (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    packetFourier (fun x => f (a * x)) t =
      |a⁻¹| • packetFourier f (t / a) := by
  change
    (∫ x : ℝ, Real.fourierChar (-(x * t)) • f (a * x)) =
      |a⁻¹| •
        ∫ y : ℝ, Real.fourierChar (-(y * (t / a))) • f y
  calc
    (∫ x : ℝ, Real.fourierChar (-(x * t)) • f (a * x))
        =
      ∫ x : ℝ,
        Real.fourierChar (-((a * x) * (t / a))) • f (a * x) := by
          apply integral_congr_ae
          filter_upwards with x
          congr 2
          field_simp [ha]
          <;> ring
    _ =
      |a⁻¹| •
        ∫ y : ℝ, Real.fourierChar (-(y * (t / a))) • f y := by
          exact Measure.integral_comp_mul_left
            (fun y : ℝ => Real.fourierChar (-(y * (t / a))) • f y) a

/-- Positive-scale form, used for the packet scale `q^A`. -/
theorem packetFourier_scale_pos (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    packetFourier (fun x => f (a * x)) t =
      a⁻¹ • packetFourier f (t / a) := by
  rw [packetFourier_scale f ha.ne' t, abs_of_pos (inv_pos.mpr ha)]

/-- Combined affine rule for a positive scale.  This is the change of
variables used for every translated bump in a prime packet. -/
theorem packetFourier_affine_pos
    (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (c t : ℝ) :
    packetFourier (fun x => f (a * (x - c))) t =
      Real.fourierChar (-c * t) •
        (a⁻¹ • packetFourier f (t / a)) := by
  calc
    packetFourier (fun x => f (a * (x - c))) t
        = packetFourier (fun x => (fun y => f (a * y)) (x - c)) t := rfl
    _ = Real.fourierChar (-c * t) •
          packetFourier (fun y => f (a * y)) t :=
      packetFourier_translate (fun y => f (a * y)) c t
    _ = Real.fourierChar (-c * t) •
          (a⁻¹ • packetFourier f (t / a)) := by
      rw [packetFourier_scale_pos f ha t]

end TNumbersLean
