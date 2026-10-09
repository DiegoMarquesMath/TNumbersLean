import TNumbersLean.KoksmaExponent
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Analysis.Normed.Group.Int
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

noncomputable section

namespace TNumbersLean
namespace RealAlgebraicData

open Polynomial
open scoped nonZeroDivisors

/-- Real algebraicity over the rational field, not over the real field. -/
abbrev isAlg (α : ℝ) : Prop := IsAlgebraic ℚ α

/-- The usual algebraic degree; the default for a transcendental real is zero. -/
def degree (α : ℝ) : ℕ := (minpoly ℚ α).natDegree

/-- Mathlib denominator clearing, applied to the rational minimal polynomial. -/
def clearedMinpoly (α : ℝ) : ℤ[X] :=
  IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ α)

/-- Divide the cleared polynomial by its integer content. It is unique up to
sign for algebraic α; for nonalgebraic α the library's primitive part is one. -/
def primitiveMinpoly (α : ℝ) : ℤ[X] := (clearedMinpoly α).primPart

/-- Radius-one Gauss norm with the ordinary integer norm: exactly the maximum
absolute coefficient, not a Weil or logarithmic height. -/
def coefficientHeight (p : ℤ[X]) : ℝ := p.gaussNorm (normAddGroupSeminorm ℤ) 1

def naiveHeight (α : ℝ) : ℝ := coefficientHeight (primitiveMinpoly α)

/-- The literal defining properties of a primitive integer minimal polynomial. -/
def IsPrimitiveMinimalPolynomial (α : ℝ) (p : ℤ[X]) : Prop :=
  p.IsPrimitive ∧ Irreducible (p.map (algebraMap ℤ ℚ)) ∧ aeval α p = 0

theorem degree_pos {α : ℝ} (hα : isAlg α) : 1 ≤ degree α :=
  minpoly.natDegree_pos hα.isIntegral

theorem degree_eq_finrank {α : ℝ} (hα : isAlg α) :
    degree α = Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) :=
  (IntermediateField.adjoin.finrank hα.isIntegral).symm

/-- Rational translation preserves actual algebraicity. -/
theorem isAlg_add_rat {α : ℝ} (hα : isAlg α) (q : ℚ) : isAlg (α + (q : ℝ)) :=
  (hα.isIntegral.add (isIntegral_algebraMap (x := q))).isAlgebraic

/-- Rational translation preserves the usual algebraic degree. -/
theorem degree_add_rat {α : ℝ} (_hα : isAlg α) (q : ℚ) :
    degree (α + (q : ℝ)) = degree α := by
  change (minpoly ℚ (α + algebraMap ℚ ℝ q)).natDegree = _
  rw [minpoly.add_algebraMap, natDegree_comp, natDegree_X_sub_C, mul_one]
  rfl

theorem clearedMinpoly_ne_zero {α : ℝ} (hα : isAlg α) : clearedMinpoly α ≠ 0 := by
  intro h
  exact minpoly.ne_zero hα.isIntegral
    (IsFractionRing.integerNormalization_eq_zero_iff.mp h)

theorem primitiveMinpoly_isPrimitive (α : ℝ) : (primitiveMinpoly α).IsPrimitive :=
  (clearedMinpoly α).isPrimitive_primPart

theorem primitiveMinpoly_ne_zero (α : ℝ) : primitiveMinpoly α ≠ 0 :=
  (clearedMinpoly α).primPart_ne_zero

/-- The constructed integer polynomial maps to a nonzero rational scalar
multiple of the monic rational minimal polynomial. -/
theorem primitiveMinpoly_map {α : ℝ} (hα : isAlg α) :
    ∃ c : ℚ, c ≠ 0 ∧
      (primitiveMinpoly α).map (algebraMap ℤ ℚ) = C c * minpoly ℚ α := by
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map
    (nonZeroDivisors ℤ) (minpoly ℚ α)
  have hb0 : (b : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have hbQ : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hc0 : (clearedMinpoly α).content ≠ 0 := by
    exact fun h => clearedMinpoly_ne_zero hα (Polynomial.content_eq_zero_iff.mp h)
  have hcQ : ((clearedMinpoly α).content : ℚ) ≠ 0 := by exact_mod_cast hc0
  have he : (clearedMinpoly α).map (algebraMap ℤ ℚ) =
      C ((clearedMinpoly α).content : ℚ) *
        (primitiveMinpoly α).map (algebraMap ℤ ℚ) := by
    conv_lhs => rw [(clearedMinpoly α).eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hb' : (clearedMinpoly α).map (algebraMap ℤ ℚ) =
      C ((b : ℤ) : ℚ) * minpoly ℚ α := by
    simpa only [clearedMinpoly, Algebra.smul_def, Polynomial.algebraMap_apply] using hb
  refine ⟨((clearedMinpoly α).content : ℚ)⁻¹ * ((b : ℤ) : ℚ),
    mul_ne_zero (inv_ne_zero hcQ) hbQ, ?_⟩
  calc
    (primitiveMinpoly α).map (algebraMap ℤ ℚ) =
        C ((clearedMinpoly α).content : ℚ)⁻¹ *
          (C ((clearedMinpoly α).content : ℚ) *
            (primitiveMinpoly α).map (algebraMap ℤ ℚ)) := by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hcQ, C_1, one_mul]
    _ = C ((clearedMinpoly α).content : ℚ)⁻¹ *
        (C ((b : ℤ) : ℚ) * minpoly ℚ α) := by rw [← he, hb']
    _ = _ := by rw [← mul_assoc, ← C_mul]

theorem primitiveMinpoly_aeval {α : ℝ} (hα : isAlg α) :
    aeval α (primitiveMinpoly α) = 0 := by
  apply aeval_primPart_eq_zero (clearedMinpoly_ne_zero hα)
  exact IsLocalization.integerNormalization_aeval_eq_zero
    (nonZeroDivisors ℤ) (minpoly ℚ α) (minpoly.aeval ℚ α)

theorem primitiveMinpoly_irreducible_map {α : ℝ} (hα : isAlg α) :
    Irreducible ((primitiveMinpoly α).map (algebraMap ℤ ℚ)) := by
  obtain ⟨c, hc, he⟩ := primitiveMinpoly_map hα
  rw [he]
  exact (associated_unit_mul_left (minpoly ℚ α) (C c)
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))).symm.irreducible
      (minpoly.irreducible hα.isIntegral)

theorem primitiveMinpoly_irreducible {α : ℝ} (hα : isAlg α) :
    Irreducible (primitiveMinpoly α) :=
  (primitiveMinpoly_isPrimitive α).irreducible_of_irreducible_map_of_injective
    Int.cast_injective (primitiveMinpoly_irreducible_map hα)

theorem primitiveMinpoly_identification {α : ℝ} (hα : isAlg α) :
    IsPrimitiveMinimalPolynomial α (primitiveMinpoly α) :=
  ⟨primitiveMinpoly_isPrimitive α, primitiveMinpoly_irreducible_map hα,
    primitiveMinpoly_aeval hα⟩

theorem primitiveMinpoly_natDegree {α : ℝ} (hα : isAlg α) :
    (primitiveMinpoly α).natDegree = degree α := by
  obtain ⟨c, hc, he⟩ := primitiveMinpoly_map hα
  calc
    (primitiveMinpoly α).natDegree =
        ((primitiveMinpoly α).map (algebraMap ℤ ℚ)).natDegree :=
      (natDegree_map_eq_of_injective Int.cast_injective _).symm
    _ = (C c * minpoly ℚ α).natDegree := congrArg natDegree he
    _ = degree α := natDegree_C_mul hc

/-- The height bounds every coefficient, including coefficients off the support. -/
theorem abs_coeff_le_coefficientHeight (p : ℤ[X]) (i : ℕ) :
    |(p.coeff i : ℝ)| ≤ coefficientHeight p := by
  have hb := p.le_gaussNorm (normAddGroupSeminorm ℤ) (by norm_num : (0 : ℝ) ≤ 1) i
  change ‖p.coeff i‖ * 1^i ≤ coefficientHeight p at hb
  simpa only [one_pow, mul_one, Int.norm_eq_abs] using hb

/-- A coefficient attains the maximum; thus this is a maximum, not just a bound. -/
theorem coefficientHeight_attained (p : ℤ[X]) :
    ∃ i, coefficientHeight p = |(p.coeff i : ℝ)| := by
  obtain ⟨i, hi⟩ := p.exists_eq_gaussNorm (normAddGroupSeminorm ℤ) 1
  exact ⟨i, by simpa [coefficientHeight, normAddGroupSeminorm, Int.norm_eq_abs] using hi⟩

theorem coefficientHeight_eq_max (p : ℤ[X]) (H : ℝ) :
    coefficientHeight p = H ↔
      (∀ i, |(p.coeff i : ℝ)| ≤ H) ∧ ∃ i, |(p.coeff i : ℝ)| = H := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := coefficientHeight_attained p
    exact ⟨fun i => h ▸ abs_coeff_le_coefficientHeight p i, i, hi.symm.trans h⟩
  · rintro ⟨hbound, i, hi⟩
    obtain ⟨j, hj⟩ := coefficientHeight_attained p
    apply le_antisymm
    · rw [hj]
      exact hbound j
    · rw [← hi]
      exact abs_coeff_le_coefficientHeight p i

theorem coefficientHeight_neg (p : ℤ[X]) : coefficientHeight (-p) = coefficientHeight p := by
  simp [coefficientHeight, Polynomial.gaussNorm, normAddGroupSeminorm]

theorem coefficientHeight_ge_one {p : ℤ[X]} (hp : p ≠ 0) :
    1 ≤ coefficientHeight p := by
  have hn : p.coeff p.natDegree ≠ 0 := by
    simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hp
  have hz : p.coeff p.natDegree ≤ -1 ∨ 1 ≤ p.coeff p.natDegree := by omega
  have hab : 1 ≤ |(p.coeff p.natDegree : ℝ)| := by
    rcases hz with hz | hz
    · have hr : (p.coeff p.natDegree : ℝ) ≤ -1 := by exact_mod_cast hz
      linarith [neg_le_abs (p.coeff p.natDegree : ℝ)]
    · have hr : (1 : ℝ) ≤ (p.coeff p.natDegree : ℝ) := by exact_mod_cast hz
      exact hr.trans (le_abs_self _)
  exact hab.trans (abs_coeff_le_coefficientHeight p p.natDegree)

theorem naiveHeight_ge_one {α : ℝ} (_hα : isAlg α) : 1 ≤ naiveHeight α :=
  coefficientHeight_ge_one (primitiveMinpoly_ne_zero α)

/-- Integer polynomial associates differ only by sign. -/
theorem associated_eq_or_neg {p q : ℤ[X]} (h : Associated p q) : p = q ∨ p = -q := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨z, hz, hC⟩ := Polynomial.isUnit_iff.mp u.isUnit
  rcases Int.isUnit_eq_one_or hz with hz | hz
  · left
    simpa [← hC, hz] using hu
  · right
    have he : -p = q := by simpa [← hC, hz] using hu
    simpa only [neg_neg] using congrArg Neg.neg he

/-- Any primitive integer minimal polynomial is the constructed one up to sign. -/
theorem primitiveMinpoly_unique_sign {α : ℝ} (hα : isAlg α) {p : ℤ[X]}
    (hp : IsPrimitiveMinimalPolynomial α p) :
    p = primitiveMinpoly α ∨ p = -primitiveMinpoly α := by
  have hroot : aeval α (p.map (algebraMap ℤ ℚ)) = 0 := by
    simpa only [aeval_map_algebraMap] using hp.2.2
  have ha : Associated (minpoly ℚ α) (p.map (algebraMap ℤ ℚ)) :=
    (minpoly.irreducible hα.isIntegral).associated_of_dvd hp.2.1 (minpoly.dvd ℚ α hroot)
  have hb : Associated (minpoly ℚ α)
      ((primitiveMinpoly α).map (algebraMap ℤ ℚ)) :=
    (minpoly.irreducible hα.isIntegral).associated_of_dvd
      (primitiveMinpoly_irreducible_map hα)
      (minpoly.dvd ℚ α (by simpa only [aeval_map_algebraMap] using primitiveMinpoly_aeval hα))
  have hab := ha.symm.trans hb
  apply associated_eq_or_neg
  apply associated_of_dvd_dvd
  · exact hp.1.dvd_of_fraction_map_dvd_fraction_map (primitiveMinpoly_isPrimitive α) hab.dvd
  · exact (primitiveMinpoly_isPrimitive α).dvd_of_fraction_map_dvd_fraction_map hp.1 hab.symm.dvd

/-- Literal agreement with the manuscript's height for either choice of sign. -/
theorem naiveHeight_eq_of_primitive_minimal {α : ℝ} (hα : isAlg α) {p : ℤ[X]}
    (hp : IsPrimitiveMinimalPolynomial α p) : naiveHeight α = coefficientHeight p := by
  rcases primitiveMinpoly_unique_sign hα hp with rfl | rfl
  · rfl
  · exact (coefficientHeight_neg _).symm

theorem degree_eq_of_primitive_minimal {α : ℝ} (hα : isAlg α) {p : ℤ[X]}
    (hp : IsPrimitiveMinimalPolynomial α p) : degree α = p.natDegree := by
  rcases primitiveMinpoly_unique_sign hα hp with rfl | rfl
  · exact (primitiveMinpoly_natDegree hα).symm
  · simpa using (primitiveMinpoly_natDegree hα).symm

/-- A real coefficient bound leaves finitely many possible integer coefficients. -/
theorem bounded_integer_coefficients_finite (H : ℝ) :
    {z : ℤ | |(z : ℝ)| ≤ H}.Finite := by
  obtain ⟨B, hB⟩ := exists_nat_gt H
  apply (Set.finite_Icc (-(B : ℤ)) (B : ℤ)).subset
  intro z hz
  have hr := abs_le.mp (hz.trans hB.le)
  constructor
  · exact_mod_cast hr.1
  · exact_mod_cast hr.2

/-- Polynomial counting uses an injective tuple of n+1 bounded integer coefficients. -/
theorem bounded_polynomials_finite (n : ℕ) (H : ℝ) :
    {p : ℤ[X] | p.natDegree ≤ n ∧ coefficientHeight p ≤ H}.Finite := by
  let f : ℤ[X] → (Fin (n+1) → ℤ) := fun p i => p.coeff i
  have hpi : {v : Fin (n+1) → ℤ | ∀ i, |(v i : ℝ)| ≤ H}.Finite :=
    Set.Finite.pi' (fun _ => bounded_integer_coefficients_finite H)
  apply Set.Finite.of_injOn (f := f) (t := {v | ∀ i, |(v i : ℝ)| ≤ H}) ?_ ?_ hpi
  · intro p hp i
    exact (abs_coeff_le_coefficientHeight p i).trans hp.2
  · intro p hp q hq he
    have hpdeg : p.natDegree ≤ n := hp.1
    have hqdeg : q.natDegree ≤ n := hq.1
    apply Polynomial.ext
    intro i
    by_cases hi : i ≤ n
    · exact congrFun he ⟨i, by omega⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i),
        coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < i)]

/-- Elementary Northcott for naive height: finitely many bounded coefficient
polynomials, each nonzero polynomial having finitely many real roots. -/
theorem northcott (n : ℕ) (H : ℝ) :
    {α : ℝ | isAlg α ∧ degree α ≤ n ∧ naiveHeight α ≤ H}.Finite := by
  let polys : Set ℤ[X] := {p | p ≠ 0 ∧ p.natDegree ≤ n ∧ coefficientHeight p ≤ H}
  have hpolys : polys.Finite := (bounded_polynomials_finite n H).subset
    (fun _ hp => hp.2)
  have hroots : (⋃ p ∈ polys, {α : ℝ | (p.map (algebraMap ℤ ℝ)).IsRoot α}).Finite := by
    apply hpolys.biUnion
    intro p hp
    apply Polynomial.finite_setOf_isRoot
    exact fun he => hp.1 (Polynomial.map_injective _ Int.cast_injective
      (by simpa using he))
  apply hroots.subset
  intro α hα
  apply Set.mem_iUnion.2
  refine ⟨primitiveMinpoly α, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
  · exact ⟨primitiveMinpoly_ne_zero α, (primitiveMinpoly_natDegree hα.1).trans_le hα.2.1,
      hα.2.2⟩
  · simpa only [Polynomial.IsRoot, eval_map, ← aeval_def] using primitiveMinpoly_aeval hα.1

end RealAlgebraicData

/-- The manuscript's actual real algebraicity, algebraic degree, and primitive
integer minimal polynomial naive height, with elementary Northcott proved. -/
def realAlgebraicApproximationSystem : AlgebraicApproximationSystem where
  isAlg := RealAlgebraicData.isAlg
  degree := RealAlgebraicData.degree
  height := RealAlgebraicData.naiveHeight
  degree_pos _ h := RealAlgebraicData.degree_pos h
  height_ge_one _ h := RealAlgebraicData.naiveHeight_ge_one h
  northcott := RealAlgebraicData.northcott

theorem realAlgebraicApproximationSystem_isAlg (α : ℝ) :
    realAlgebraicApproximationSystem.isAlg α ↔ IsAlgebraic ℚ α := Iff.rfl

theorem realAlgebraicApproximationSystem_degree {α : ℝ}
    (hα : IsAlgebraic ℚ α) :
    realAlgebraicApproximationSystem.degree α =
      (RealAlgebraicData.primitiveMinpoly α).natDegree :=
  (RealAlgebraicData.primitiveMinpoly_natDegree hα).symm

theorem realAlgebraicApproximationSystem_height {α : ℝ} {p : Polynomial ℤ}
    (hα : IsAlgebraic ℚ α)
    (hp : RealAlgebraicData.IsPrimitiveMinimalPolynomial α p) :
    realAlgebraicApproximationSystem.height α = RealAlgebraicData.coefficientHeight p :=
  RealAlgebraicData.naiveHeight_eq_of_primitive_minimal hα hp

end TNumbersLean
