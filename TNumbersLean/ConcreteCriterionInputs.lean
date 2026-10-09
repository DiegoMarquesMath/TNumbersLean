import TNumbersLean.ConcreteSchedule
import TNumbersLean.ConcreteAlgebraicData
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion

noncomputable section

namespace TNumbersLean
open Polynomial

/-- The manuscript's positive real d-th root of two. -/
def theta (d : ℕ) : ℝ := (2 : ℝ) ^ (d : ℝ)⁻¹

theorem theta_pos (d : ℕ) : 0 < theta d := Real.rpow_pos_of_pos (by norm_num) _

theorem theta_pow {d : ℕ} (hd : 2 ≤ d) : theta d ^ d = 2 := by
  exact Real.rpow_inv_natCast_pow (by norm_num) (by omega)

theorem theta_le_two {d : ℕ} (hd : 2 ≤ d) : theta d ≤ 2 := by
  have hr : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hi : (d : ℝ)⁻¹ ≤ 1 := by simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hr)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hi

/-- Eisenstein at the prime integer 2, without a degree hypothesis on theta. -/
theorem theta_polynomial_irreducible {d : ℕ} (hd : 2 ≤ d) :
    Irreducible (X ^ d - C (2 : ℤ)) := by
  have hn : d ≠ 0 := by omega
  have hm := monic_X_pow_sub_C (2 : ℤ) hn
  apply irreducible_of_eisenstein_criterion
    ((Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr
      (Nat.prime_iff_prime_int.mp Nat.prime_two))
  · rw [hm.leadingCoeff, Ideal.mem_span_singleton]
    norm_num
  · intro i hi
    have hid : i < d := by
      rw [degree_X_pow_sub_C (by omega : 0 < d)] at hi
      exact_mod_cast hi
    rw [Ideal.mem_span_singleton]
    by_cases hi0 : i = 0
    · subst i
      norm_num [coeff_sub, coeff_X_pow, show (0 : ℕ) ≠ d by omega]
    · simp only [coeff_sub, coeff_X_pow, coeff_C, if_neg (show i ≠ d by omega),
        if_neg hi0, sub_zero, dvd_zero]
  · rw [degree_X_pow_sub_C (by omega : 0 < d)]
    exact_mod_cast (show 0 < d by omega)
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num [coeff_sub, coeff_X_pow, show (0 : ℕ) ≠ d by omega]
  · exact hm.isPrimitive

theorem theta_minpoly {d : ℕ} (hd : 2 ≤ d) :
    minpoly ℚ (theta d) = X ^ d - C (2 : ℚ) := by
  have hi := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (monic_X_pow_sub_C (2 : ℤ) (by omega : d ≠ 0)).isPrimitive).mp
    (theta_polynomial_irreducible hd)
  have hiQ : Irreducible (X ^ d - C (2 : ℚ)) := by simpa using hi
  exact (minpoly.eq_of_irreducible_of_monic hiQ
    (by simp [theta_pow hd]) (monic_X_pow_sub_C _ (by omega))).symm

theorem theta_algebraic {d : ℕ} (hd : 2 ≤ d) : RealAlgebraicData.isAlg (theta d) := by
  apply IsIntegral.isAlgebraic
  exact ⟨X ^ d - C (2 : ℚ), monic_X_pow_sub_C _ (by omega), by simp [theta_pow hd]⟩

theorem theta_degree {d : ℕ} (hd : 2 ≤ d) : RealAlgebraicData.degree (theta d) = d := by
  rw [RealAlgebraicData.degree, theta_minpoly hd, natDegree_X_pow_sub_C]

/-- Rational translations of theta have actual degree d. -/
theorem theta_translate_degree {d : ℕ} (hd : 2 ≤ d) (r : ℚ) :
    RealAlgebraicData.degree (theta d + (r : ℝ)) = d := by
  rw [RealAlgebraicData.degree_add_rat (theta_algebraic hd), theta_degree hd]

/-- Equations (3.7)--(3.8), retaining reducedness and their literal source error. -/
def StageWitness (t : ScheduleThresholds) (x : ℝ) (k : ℕ) (p : ℤ) (q : ℕ) : Prop :=
  0 < q ∧ Nat.Coprime p.natAbs q ∧
    t.concreteQ k ≤ q ∧ q < 2 * t.concreteQ k ∧
    |x - theta (t.concreteDegree k) - (p : ℝ) / (q : ℝ)| ≤
      (1 / 4 : ℝ) * (q : ℝ) ^ (-(t.concreteExponent k : ℝ))

/-- The literal construction set: x belongs to J and has a reduced rational
witness at every stage. Lean k corresponds to manuscript k+1. For the paper,
J is the fixed bounded open interval; no center conclusions enter this set. -/
def MemE (t : ScheduleThresholds) (J : Set ℝ) (x : ℝ) : Prop :=
  x ∈ J ∧ ∀ k, ∃ p : ℤ, ∃ q : ℕ, StageWitness t x k p q

theorem memE_stage_witness {t : ScheduleThresholds} {J : Set ℝ} {x : ℝ}
    (hE : MemE t J x) (k : ℕ) : ∃ p : ℤ, ∃ q : ℕ, StageWitness t x k p q := hE.2 k

namespace MemE
variable {t : ScheduleThresholds} {J : Set ℝ} {x : ℝ} (hE : MemE t J x)

def numerator (k : ℕ) : ℤ := Classical.choose (memE_stage_witness hE k)
def denominator (k : ℕ) : ℕ := Classical.choose (Classical.choose_spec (memE_stage_witness hE k))

theorem witness_spec (k : ℕ) : StageWitness t x k (hE.numerator k) (hE.denominator k) :=
  Classical.choose_spec (Classical.choose_spec (memE_stage_witness hE k))

theorem denominator_pos (k : ℕ) : 0 < hE.denominator k := (hE.witness_spec k).1

theorem reduced (k : ℕ) : Nat.Coprime (hE.numerator k).natAbs (hE.denominator k) :=
  (hE.witness_spec k).2.1

theorem denominator_block (k : ℕ) :
    t.concreteQ k ≤ hE.denominator k ∧ hE.denominator k < 2 * t.concreteQ k :=
  ⟨(hE.witness_spec k).2.2.1, (hE.witness_spec k).2.2.2.1⟩

def rational (k : ℕ) : ℚ := (hE.numerator k : ℚ) / (hE.denominator k : ℚ)
def center (k : ℕ) : ℝ := theta (t.concreteDegree k) + (hE.rational k : ℝ)

theorem rational_cast (k : ℕ) : (hE.rational k : ℝ) =
    (hE.numerator k : ℝ) / (hE.denominator k : ℝ) := by simp [rational]

theorem source_approximation (k : ℕ) :
    |x - hE.center k| ≤ (1 / 4 : ℝ) * (hE.denominator k : ℝ) ^
      (-(t.concreteExponent k : ℝ)) := by
  simpa only [center, rational_cast, sub_add_eq_sub_sub] using (hE.witness_spec k).2.2.2.2

theorem center_algebraic (k : ℕ) : RealAlgebraicData.isAlg (hE.center k) :=
  RealAlgebraicData.isAlg_add_rat (theta_algebraic (t.concreteDegree_ge_two k)) _

theorem center_exact_degree (k : ℕ) : RealAlgebraicData.degree (hE.center k) = t.concreteDegree k :=
  theta_translate_degree (t.concreteDegree_ge_two k) _

/-- Source error is at most one, using the certified denominator block and Q≥4. -/
theorem source_error_le_one (k : ℕ) : |x - hE.center k| ≤ 1 := by
  have hq : (1 : ℝ) ≤ (hE.denominator k : ℝ) := by
    exact_mod_cast (show 1 ≤ hE.denominator k by have := hE.denominator_pos k; omega)
  have hr : (hE.denominator k : ℝ) ^ (-(t.concreteExponent k : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hs := hE.source_approximation k
  nlinarith

theorem center_mem_bounds {R : ℝ} (hJ : J ⊆ Set.Ioo (-R) R) (k : ℕ) :
    hE.center k ∈ Set.Icc (-R - 1) (R + 1) := by
  have hx : |x| < R := abs_lt.mpr (hJ hE.1)
  have he : |hE.center k - x| ≤ 1 := by simpa only [abs_sub_comm] using hE.source_error_le_one k
  have hc : |hE.center k| ≤ R + 1 := by
    have ha := abs_add_le (hE.center k - x) x
    rw [sub_add_cancel] at ha
    linarith
  have := abs_le.mp hc
  constructor <;> linarith

theorem rational_bound {R : ℝ} (hJ : J ⊆ Set.Ioo (-R) R) (k : ℕ) :
    |(hE.numerator k : ℝ) / (hE.denominator k : ℝ)| ≤ R + 3 := by
  have hb := hE.center_mem_bounds hJ k
  have hc : |hE.center k| ≤ R + 1 := abs_le.mpr ⟨by linarith [hb.1], hb.2⟩
  have ht : |theta (t.concreteDegree k)| ≤ 2 := by
    rw [abs_of_pos (theta_pos _)]
    exact theta_le_two (t.concreteDegree_ge_two k)
  have ha := abs_sub (hE.center k) (theta (t.concreteDegree k))
  have he : hE.center k - theta (t.concreteDegree k) =
      (hE.numerator k : ℝ) / (hE.denominator k : ℝ) := by
    rw [center, rational_cast]
    ring
  rw [he] at ha
  linarith
end MemE

/-- Only (2.2) and Lemma 2.1. R is the fixed manuscript bound on J. No
proposition conclusion, source approximation, or algebraic degree is assumed. -/
structure SectionTwoInputs (t : ScheduleThresholds) (R : ℝ) where
  heightConstant : ℕ → ℝ
  heightConstant_ge_one : ∀ d, 2 ≤ d → 1 ≤ heightConstant d
  height_comparison : ∀ d, 2 ≤ d → ∀ p : ℤ, ∀ q : ℕ, 0 < q →
    Nat.Coprime p.natAbs q → |(p : ℝ) / (q : ℝ)| ≤ R + 3 →
    (q : ℝ)^d ≤ RealAlgebraicData.naiveHeight (theta d + (p : ℝ) / (q : ℝ)) ∧
    RealAlgebraicData.naiveHeight (theta d + (p : ℝ) / (q : ℝ)) ≤ heightConstant d * (q : ℝ)^d
  separation : ∀ D d n : ℕ, 2 ≤ d → d ≤ D → 1 ≤ n → n < d →
    ∀ Q : ℝ, (t.T D : ℝ) ≤ Q → ∀ p : ℤ, ∀ q : ℕ, Q ≤ (q : ℝ) →
    (q : ℝ) < 2 * Q → theta d + (p : ℝ) / (q : ℝ) ∈ Set.Icc (-R - 1) (R + 1) →
    ∀ β : ℝ, RealAlgebraicData.isAlg β → RealAlgebraicData.degree β ≤ n →
    Q ^ (-K (n : ℝ) - 1) * RealAlgebraicData.naiveHeight β ^ (-(n : ℝ) - 2) ≤
      |theta d + (p : ℝ) / (q : ℝ) - β|

/-- The actual centers selected from E, with only Section 2 height and
separation consequences external. The concrete threshold discharges Lemma 2.1. -/
def concreteCriterionInputs (t : ScheduleThresholds) (J : Set ℝ) (R : ℝ)
    (_hR : 2 ≤ R) (hJ : J ⊆ Set.Ioo (-R) R) (x : ℝ) (hE : MemE t J x)
    (H : SectionTwoInputs t R) :
    CriterionInputs realAlgebraicApproximationSystem t.concreteCriterionSchedule x where
  center := hE.center
  q := hE.denominator
  denominator_pos := hE.denominator_pos
  denominator_lower k := by
    change (t.concreteQ k : ℝ) ≤ (hE.denominator k : ℝ)
    exact_mod_cast (hE.denominator_block k).1
  denominator_upper k := by
    change (hE.denominator k : ℝ) < 2 * (t.concreteQ k : ℝ)
    exact_mod_cast (hE.denominator_block k).2
  center_algebraic := hE.center_algebraic
  center_exact_degree := hE.center_exact_degree
  source_approximation := hE.source_approximation
  heightConstant := H.heightConstant
  heightConstant_ge_one := H.heightConstant_ge_one
  center_height_lower k := by
    have hh := H.height_comparison _ (t.concreteDegree_ge_two k) _ _
      (hE.denominator_pos k) (hE.reduced k) (hE.rational_bound hJ k)
    simpa only [MemE.center, MemE.rational_cast] using hh.1
  center_height_upper k := by
    have hh := H.height_comparison _ (t.concreteDegree_ge_two k) _ _
      (hE.denominator_pos k) (hE.reduced k) (hE.rational_bound hJ k)
    simpa only [MemE.center, MemE.rational_cast] using hh.2
  translated_center_separation n k hn hk β hβ hdeg := by
    have hT : (t.T (t.concreteDegree k) : ℝ) ≤ (t.concreteQ k : ℝ) := by
      exact_mod_cast t.concrete_threshold k
    have hl : (t.concreteQ k : ℝ) ≤ (hE.denominator k : ℝ) := by
      exact_mod_cast (hE.denominator_block k).1
    have hu : (hE.denominator k : ℝ) < 2 * (t.concreteQ k : ℝ) := by
      exact_mod_cast (hE.denominator_block k).2
    have hb : theta (t.concreteDegree k) + (hE.numerator k : ℝ) / (hE.denominator k : ℝ) ∈
        Set.Icc (-R - 1) (R + 1) := by
      simpa only [MemE.center, MemE.rational_cast] using hE.center_mem_bounds hJ k
    have hs := H.separation _ _ n (t.concreteDegree_ge_two k) le_rfl hn hk
      _ hT _ _ hl hu hb β hβ hdeg
    simpa only [MemE.center, MemE.rational_cast] using hs

end TNumbersLean
