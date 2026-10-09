import Mathlib.Analysis.Fourier.ZMod
import Mathlib.RingTheory.Int.Basic

namespace TNumbersLean

open Complex
open scoped BigOperators

/-- The complete additive-character sum over residues modulo `q` which
appears in the Fourier coefficient of a single prime packet. -/
noncomputable def fullPacketResidueSum (q : ℕ) [NeZero q] (ell : ℤ) : ℂ :=
  ∑ a : ZMod q, ZMod.stdAddChar (-(a * (ell : ZMod q)))

/-- Orthogonality of the standard additive character, expressed in the
integer-divisibility form used in the manuscript. -/
theorem fullPacketResidueSum_eq (q : ℕ) [NeZero q] (ell : ℤ) :
    fullPacketResidueSum q ell =
      if q ∣ ell.natAbs then (q : ℂ) else 0 := by
  by_cases hd : q ∣ ell.natAbs
  · have hz : (ell : ZMod q) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]
      exact hd
    simp [fullPacketResidueSum, hz, hd, ZMod.card]
  · have hz : (ell : ZMod q) ≠ 0 := by
      intro hzero
      apply hd
      have hi : (q : ℤ) ∣ ell :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd ell q).mp hzero
      exact Int.natCast_dvd.mp hi
    have hsum :=
      AddChar.sum_mulShift
        (ψ := ZMod.stdAddChar (N := q))
        (-(ell : ZMod q))
        (ZMod.isPrimitive_stdAddChar q)
    have hneg : (-(ell : ZMod q)) ≠ 0 := neg_ne_zero.mpr hz
    rw [fullPacketResidueSum]
    simp [hd]
    simpa [mul_neg, hneg, ZMod.card] using hsum

/-- The nonzero-residue character sum.  This is the finite arithmetic factor
obtained after removing the residue class `0` from the full character sum. -/
noncomputable def packetResidueSum (q : ℕ) [NeZero q] (ell : ℤ) : ℂ :=
  fullPacketResidueSum q ell - 1

/-- Exact Ramanujan-sum dichotomy behind equation (5.3) of the manuscript:
the nonzero residue classes contribute `q - 1` when `q ∣ ell`, and `-1`
otherwise. -/
theorem packetResidueSum_eq (q : ℕ) [NeZero q] (ell : ℤ) :
    packetResidueSum q ell =
      if q ∣ ell.natAbs then (q : ℂ) - 1 else -1 := by
  rw [packetResidueSum, fullPacketResidueSum_eq]
  by_cases hd : q ∣ ell.natAbs <;> simp [hd]

/-- The normalized residue factor occurring in the Fourier coefficient of
`g_{q,A,theta}`. -/
noncomputable def packetResidueFactor (q : ℕ) [NeZero q] (ell : ℤ) : ℂ :=
  packetResidueSum q ell / ((q : ℂ) - 1)

/-- For prime `q`, the normalized residue factor is exactly `1` on
frequencies divisible by `q`, and `-1/(q-1)` otherwise. -/
theorem packetResidueFactor_eq {q : ℕ} [NeZero q]
    (hq : Nat.Prime q) (ell : ℤ) :
    packetResidueFactor q ell =
      if q ∣ ell.natAbs then 1 else -(1 / ((q : ℂ) - 1)) := by
  have hden : ((q : ℂ) - 1) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hq.ne_one
  rw [packetResidueFactor, packetResidueSum_eq]
  by_cases hd : q ∣ ell.natAbs
  · simp [hd, hden]
  · simp [hd, div_eq_mul_inv]

/-- Equivalent form matching the parenthesis in the manuscript coefficient:
`q/(q-1) * 1_{q|ell} - 1/(q-1)`. -/
theorem packetResidueFactor_eq_manuscript {q : ℕ} [NeZero q]
    (hq : Nat.Prime q) (ell : ℤ) :
    packetResidueFactor q ell =
      ((q : ℂ) / ((q : ℂ) - 1)) *
          (if q ∣ ell.natAbs then 1 else 0) -
        1 / ((q : ℂ) - 1) := by
  rw [packetResidueFactor_eq hq ell]
  have hden : ((q : ℂ) - 1) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hq.ne_one
  by_cases hd : q ∣ ell.natAbs
  · simp [hd]
    field_simp
  · simp [hd]


/-- Identification of the real Fourier phase at a rational point with the
standard additive character modulo `q`.  This is the bridge between the
analytic phase in a periodized bump and the finite residue sum. -/
theorem fourierChar_rational_phase_eq_stdAddChar
    (q : ℕ) [NeZero q] (a ell : ℤ) :
    (Real.fourierChar
        (-((a : ℝ) / (q : ℝ) * (ell : ℝ))) : ℂ) =
      ZMod.stdAddChar
        (-((a : ZMod q) * (ell : ZMod q))) := by
  have harg :
      -((a : ZMod q) * (ell : ZMod q)) =
        ((-(a * ell) : ℤ) : ZMod q) := by
    push_cast
    ring
  rw [harg, ZMod.stdAddChar_coe, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

end TNumbersLean
