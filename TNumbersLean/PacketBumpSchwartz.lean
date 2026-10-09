import TNumbersLean.PacketBumpFourier
import TNumbersLean.SchwartzPeriodization

namespace TNumbersLean

open MeasureTheory
open scoped ContDiff

theorem paperBumpComplex_hasCompactSupport :
    HasCompactSupport paperBumpComplex := by
  have h :=
    paperBump_hasCompactSupport.comp_left
      (show Complex.ofReal (0 : ℝ) = 0 by simp)
  simpa [paperBumpComplex, Function.comp_def] using h

theorem paperBumpComplex_contDiff :
    ContDiff ℝ ∞ paperBumpComplex := by
  have h := Complex.ofRealCLM.contDiff.comp paperBump_contDiff
  simpa [paperBumpComplex, Function.comp_def] using h

/-- The normalized paper bump, bundled as a Schwartz function. -/
noncomputable def paperBumpSchwartz : SchwartzMap ℝ ℂ :=
  paperBumpComplex_hasCompactSupport.toSchwartzMap paperBumpComplex_contDiff

@[simp]
theorem paperBumpSchwartz_apply (x : ℝ) :
    paperBumpSchwartz x = paperBumpComplex x := rfl

/-- Affine form of one packet bump, written in the shape best suited to
compact-support and Schwartz-space lemmas. -/
noncomputable def affinePacketBumpComplex
    (q A : ℕ) (θ₀ : ℝ) (p : ℤ) (x : ℝ) : ℂ :=
  paperBumpComplex
    (((q : ℝ) ^ A) * (x - (θ₀ + (p : ℝ) / (q : ℝ))))

theorem affinePacketBumpComplex_eq
    (q A : ℕ) (θ₀ : ℝ) (p : ℤ) :
    affinePacketBumpComplex q A θ₀ p =
      complexPacketBumpTerm q A θ₀ p := by
  funext x
  exact (complexPacketBumpTerm_eq_affine q A θ₀ p x).symm

theorem affinePacketBumpComplex_contDiff
    (q A : ℕ) (θ₀ : ℝ) (p : ℤ) :
    ContDiff ℝ ∞ (affinePacketBumpComplex q A θ₀ p) := by
  have hinner :
      ContDiff ℝ ∞
        (fun x : ℝ =>
          ((q : ℝ) ^ A) * (x - (θ₀ + (p : ℝ) / (q : ℝ)))) := by
    fun_prop
  exact paperBumpComplex_contDiff.comp hinner

theorem affinePacketBumpComplex_hasCompactSupport
    {q A : ℕ} (hq : 0 < q) (θ₀ : ℝ) (p : ℤ) :
    HasCompactSupport (affinePacketBumpComplex q A θ₀ p) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  have hscale : ((q : ℝ) ^ A) ≠ 0 := (pow_pos hqR A).ne'
  have hs :
      HasCompactSupport
        (fun x : ℝ => paperBumpComplex (((q : ℝ) ^ A) * x)) := by
    simpa [smul_eq_mul] using
      paperBumpComplex_hasCompactSupport.comp_smul hscale
  have ht :=
    hs.comp_homeomorph
      (Homeomorph.addRight (-(θ₀ + (p : ℝ) / (q : ℝ))))
  simpa only [affinePacketBumpComplex, sub_eq_add_neg, Function.comp_def] using ht

/-- Every individual packet bump is a Schwartz function. -/
noncomputable def affinePacketBumpSchwartz
    {q A : ℕ} (hq : 0 < q) (θ₀ : ℝ) (p : ℤ) : SchwartzMap ℝ ℂ :=
  (affinePacketBumpComplex_hasCompactSupport hq θ₀ p).toSchwartzMap
    (affinePacketBumpComplex_contDiff q A θ₀ p)

@[simp]
theorem affinePacketBumpSchwartz_apply
    {q A : ℕ} (hq : 0 < q) (θ₀ : ℝ) (p : ℤ) (x : ℝ) :
    affinePacketBumpSchwartz (A := A) hq θ₀ p x =
      affinePacketBumpComplex q A θ₀ p x := rfl

end TNumbersLean
