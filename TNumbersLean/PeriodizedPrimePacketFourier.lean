import TNumbersLean.PeriodizedPacketBumpFourier
import TNumbersLean.PacketFourierArithmetic

namespace TNumbersLean

open Complex
open scoped BigOperators FourierTransform

/-- The sum of the rational Fourier phases over the nonzero residue classes
modulo `q`.  This is the finite phase sum left after periodizing the
single-prime packet. -/
noncomputable def packetPhaseSum (q : ℕ) [NeZero q] (ell : ℤ) : ℂ :=
  ∑ a ∈ (Finset.univ.erase (0 : ZMod q)),
    (Real.fourierChar
      (-((a.val : ℝ) / (q : ℝ) * (ell : ℝ))) : ℂ)

/-- The Fourier phase attached to a residue class is the standard additive
character of that class modulo `q`. -/
theorem fourierChar_zmod_phase_eq_stdAddChar
    (q : ℕ) [NeZero q] (a : ZMod q) (ell : ℤ) :
    (Real.fourierChar
        (-((a.val : ℝ) / (q : ℝ) * (ell : ℝ))) : ℂ) =
      ZMod.stdAddChar (-(a * (ell : ZMod q))) := by
  simpa using
    (fourierChar_rational_phase_eq_stdAddChar
      q (a.val : ℤ) ell)

/-- The sum of the standard additive character over the nonzero residue
classes is the residue sum used in the single-prime coefficient. -/
theorem packetStdAddCharSum_eq_packetResidueSum
    (q : ℕ) [NeZero q] (ell : ℤ) :
    (∑ a ∈ (Finset.univ.erase (0 : ZMod q)),
      ZMod.stdAddChar (-(a * (ell : ZMod q)))) =
      packetResidueSum q ell := by
  rw [packetResidueSum, fullPacketResidueSum]
  have h :=
    Finset.add_sum_erase
      (Finset.univ : Finset (ZMod q))
      (fun a : ZMod q =>
        ZMod.stdAddChar (-(a * (ell : ZMod q))))
      (by simp : (0 : ZMod q) ∈ (Finset.univ : Finset (ZMod q)))
  rw [← h]
  simp

/-- The nonzero rational phase sum is exactly the Ramanujan-type residue
sum isolated in `PacketFourierArithmetic`. -/
theorem packetPhaseSum_eq_packetResidueSum
    (q : ℕ) [NeZero q] (ell : ℤ) :
    packetPhaseSum q ell = packetResidueSum q ell := by
  rw [packetPhaseSum]
  simp_rw [fourierChar_zmod_phase_eq_stdAddChar]
  exact packetStdAddCharSum_eq_packetResidueSum q ell

/-- Splitting the phase of an affine packet center into its common
translation part and its residue-class part. -/
theorem fourierChar_affine_zmod_phase_factor
    (q : ℕ) [NeZero q] (θ₀ : ℝ) (a : ZMod q) (ell : ℤ) :
    (Real.fourierChar
        (-(θ₀ + (a.val : ℝ) / (q : ℝ)) * (ell : ℝ)) : ℂ) =
      (Real.fourierChar (-θ₀ * (ell : ℝ)) : ℂ) *
        ZMod.stdAddChar (-(a * (ell : ZMod q))) := by
  have harg :
      -(θ₀ + (a.val : ℝ) / (q : ℝ)) * (ell : ℝ) =
        -θ₀ * (ell : ℝ) +
          (-((a.val : ℝ) / (q : ℝ) * (ell : ℝ))) := by
    ring
  rw [harg, Real.fourierChar.map_add_eq_mul, Circle.coe_mul]
  rw [fourierChar_zmod_phase_eq_stdAddChar]

/-- Variant of the affine phase factorization matching the nested
integer-to-real coercion produced by the periodized bump formula. -/
theorem fourierChar_affine_zmod_phase_factor_intVal
    (q : ℕ) [NeZero q] (θ₀ : ℝ) (a : ZMod q) (ell : ℤ) :
    (Real.fourierChar
        (-(θ₀ + (((a.val : ℤ) : ℝ)) / (q : ℝ)) * (ell : ℝ)) : ℂ) =
      (Real.fourierChar (-θ₀ * (ell : ℝ)) : ℂ) *
        ZMod.stdAddChar (-(a * (ell : ZMod q))) := by
  have hval : (((a.val : ℤ) : ℝ)) = (a.val : ℝ) := by
    norm_cast
  rw [hval]
  exact fourierChar_affine_zmod_phase_factor q θ₀ a ell

/-- The Fourier coefficient obtained by summing the periodized affine bumps
over the nonzero residue classes and inserting the manuscript normalization
of the single-prime packet. -/
noncomputable def periodizedPrimePacketCoeff
    {q A : ℕ} [NeZero q] (hq : Nat.Prime q) (θ₀ : ℝ) (ell : ℤ) : ℂ :=
  ((q : ℂ) ^ A / ((q : ℂ) - 1)) *
    ∑ a ∈ (Finset.univ.erase (0 : ZMod q)),
      fourierCoeff
        (periodizedAffinePacketBump
          (A := A) hq.pos θ₀ (a.val : ℤ)) ell

/-- Exact reduction of the periodized single-prime coefficient to the
normalized finite residue factor.  All dependence on the residue classes is
now contained in `packetResidueFactor`. -/
theorem periodizedPrimePacketCoeff_eq_residueFactor
    {q A : ℕ} [NeZero q] (hq : Nat.Prime q) (θ₀ : ℝ) (ell : ℤ) :
    periodizedPrimePacketCoeff (A := A) hq θ₀ ell =
      (Real.fourierChar (-θ₀ * (ell : ℝ)) : ℂ) *
        packetFourier paperBumpComplex
          ((ell : ℝ) / ((q : ℝ) ^ A)) *
        packetResidueFactor q ell := by
  rw [periodizedPrimePacketCoeff]
  simp_rw [fourierCoeff_periodizedAffinePacketBump_eq
    (A := A) hq.pos θ₀]
  simp only [Circle.smul_def, Complex.real_smul, smul_eq_mul]
  simp_rw [fourierChar_affine_zmod_phase_factor_intVal q θ₀]
  have hsum :
      (∑ a ∈ (Finset.univ.erase (0 : ZMod q)),
        (Real.fourierChar (-θ₀ * (ell : ℝ)) : ℂ) *
          ZMod.stdAddChar (-(a * (ell : ZMod q))) *
          (((((q : ℝ) ^ A)⁻¹ : ℝ) : ℂ) *
            packetFourier paperBumpComplex
              ((ell : ℝ) / ((q : ℝ) ^ A)))) =
        (Real.fourierChar (-θ₀ * (ell : ℝ)) : ℂ) *
          (((((q : ℝ) ^ A)⁻¹ : ℝ) : ℂ) *
            packetFourier paperBumpComplex
              ((ell : ℝ) / ((q : ℝ) ^ A))) *
          packetResidueSum q ell := by
    rw [← packetStdAddCharSum_eq_packetResidueSum q ell]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hsum]
  rw [packetResidueFactor]
  have hqC : (q : ℂ) ≠ 0 := by
    exact_mod_cast hq.ne_zero
  have hscaleC : (q : ℂ) ^ A ≠ 0 := pow_ne_zero A hqC
  push_cast
  field_simp [hscaleC]
  ring

/-- The exact single-prime Fourier coefficient in the form displayed in the
manuscript. -/
theorem periodizedPrimePacketCoeff_eq_manuscript
    {q A : ℕ} [NeZero q] (hq : Nat.Prime q) (θ₀ : ℝ) (ell : ℤ) :
    periodizedPrimePacketCoeff (A := A) hq θ₀ ell =
      (Real.fourierChar (-θ₀ * (ell : ℝ)) : ℂ) *
        packetFourier paperBumpComplex
          ((ell : ℝ) / ((q : ℝ) ^ A)) *
        (((q : ℂ) / ((q : ℂ) - 1)) *
            (if q ∣ ell.natAbs then 1 else 0) -
          1 / ((q : ℂ) - 1)) := by
  rw [periodizedPrimePacketCoeff_eq_residueFactor (A := A) hq θ₀ ell]
  rw [packetResidueFactor_eq_manuscript hq ell]

end TNumbersLean
