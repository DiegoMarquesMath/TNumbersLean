import TNumbersLean.ConcreteCriterionInputs
import TNumbersLean.PropositionThreeTwo

namespace TNumbersLean

/-- Concrete Proposition 3.2, conditional only on the stated Section 2
estimates. The height threshold is chosen before both the point y in E and β.
All proof content is supplied by the previously certified proposition and its
uniform separation theorem; no Diophantine argument is repeated here. -/
theorem concrete_proposition_three_two (t : ScheduleThresholds) (J : Set ℝ) (R : ℝ)
    (hR : 2 ≤ R) (hJ : J ⊆ Set.Ioo (-R) R) (x : ℝ) (hE : MemE t J x)
    (H : SectionTwoInputs t R) :
    (¬ IsAlgebraic ℚ x) ∧
    (∀ n, 1 ≤ n → ∃ Hₙ : ℝ, 2 ≤ Hₙ ∧ ∀ y, MemE t J y → ∀ β,
      IsAlgebraic ℚ β → RealAlgebraicData.degree β ≤ n → Hₙ ≤ RealAlgebraicData.naiveHeight β →
        RealAlgebraicData.naiveHeight β ^ (-propositionB n - 1) ≤ |y - β|) ∧
    (∀ n, 1 ≤ n → realAlgebraicApproximationSystem.wStar x n ≤ (propositionB n : EReal)) ∧
    (∀ d, 2 ≤ d → (recurrentW d : EReal) ≤ realAlgebraicApproximationSystem.wStar x d) ∧
    (∀ L : ℝ, ∀ N : ℕ, ∃ n ≥ N,
      (L : EReal) ≤ realAlgebraicApproximationSystem.normalizedWStar x n) ∧
    Filter.Tendsto (realAlgebraicApproximationSystem.normalizedWStar x)
      Filter.atTop (nhds (⊤ : EReal)) ∧
    Filter.limsup (realAlgebraicApproximationSystem.normalizedWStar x) Filter.atTop = ⊤ ∧
    realAlgebraicApproximationSystem.IsTNumber x := by
  have hp := proposition_three_two (concreteCriterionInputs t J R hR hJ x hE H)
  refine ⟨hp.1, ?_, hp.2.2⟩
  intro n hn
  obtain ⟨Hₙ, hHₙ, hbound⟩ := CriterionInputs.global_separation_uniform
    (S := realAlgebraicApproximationSystem) (s := t.concreteCriterionSchedule) n hn
  exact ⟨Hₙ, hHₙ, fun y hy => hbound (concreteCriterionInputs t J R hR hJ y hy H)⟩

variable {t : ScheduleThresholds} {J : Set ℝ} {R x : ℝ}
    (hR : 2 ≤ R) (hJ : J ⊆ Set.Ioo (-R) R) (hE : MemE t J x) (H : SectionTwoInputs t R)

include hR hJ hE H

theorem concrete_transcendence : ¬ IsAlgebraic ℚ x :=
  (concrete_proposition_three_two t J R hR hJ x hE H).1

/-- Equation (3.10), with Hₙ uniform in all points of E and all targets β. -/
theorem concrete_global_separation (n : ℕ) (hn : 1 ≤ n) :
    ∃ Hₙ : ℝ, 2 ≤ Hₙ ∧ ∀ y, MemE t J y → ∀ β,
      IsAlgebraic ℚ β → RealAlgebraicData.degree β ≤ n → Hₙ ≤ RealAlgebraicData.naiveHeight β →
        RealAlgebraicData.naiveHeight β ^ (-propositionB n - 1) ≤ |y - β| :=
  (concrete_proposition_three_two t J R hR hJ x hE H).2.1 n hn

theorem concrete_upper_wStar (n : ℕ) (hn : 1 ≤ n) :
    realAlgebraicApproximationSystem.wStar x n ≤ (propositionB n : EReal) :=
  (concrete_proposition_three_two t J R hR hJ x hE H).2.2.1 n hn

theorem concrete_lower_wStar (d : ℕ) (hd : 2 ≤ d) :
    (recurrentW d : EReal) ≤ realAlgebraicApproximationSystem.wStar x d :=
  (concrete_proposition_three_two t J R hR hJ x hE H).2.2.2.1 d hd

theorem concrete_isTNumber : realAlgebraicApproximationSystem.IsTNumber x :=
  (concrete_proposition_three_two t J R hR hJ x hE H).2.2.2.2.2.2.2

end TNumbersLean
