import Mathlib

noncomputable section

namespace TNumbersLean

/-- Abstract naive algebraic height; Northcott is an explicit external input. -/
structure AlgebraicApproximationSystem where
  isAlg : ℝ → Prop
  degree : ℝ → ℕ
  height : ℝ → ℝ
  degree_pos : ∀ α, isAlg α → 1 ≤ degree α
  height_ge_one : ∀ α, isAlg α → 1 ≤ height α
  northcott : ∀ n H, {α | isAlg α ∧ degree α ≤ n ∧ height α ≤ H}.Finite

namespace AlgebraicApproximationSystem

variable (S : AlgebraicApproximationSystem)

/-- The set in (1.1). Infinitude is of real values, not of witnesses or indices. -/
def approximants (x : ℝ) (n : ℕ) (w : ℝ) : Set ℝ :=
  {α | S.isAlg α ∧ S.degree α ≤ n ∧
    0 < |x - α| ∧ |x - α| < S.height α ^ (-w - 1)}

def admissibleExponents (x : ℝ) (n : ℕ) : Set ℝ :=
  {w | (S.approximants x n w).Infinite}

/-- Extended-real supremum, retaining both infinite and empty-set cases. -/
def wStar (x : ℝ) (n : ℕ) : EReal :=
  ⨆ w ∈ S.admissibleExponents x n, (w : EReal)

theorem admissible_le_wStar {x w : ℝ} {n : ℕ}
    (hw : w ∈ S.admissibleExponents x n) : (w : EReal) ≤ S.wStar x n :=
  le_iSup_of_le w (le_iSup_of_le hw le_rfl)

/-- Northcott removes all bounded-height exceptions in the upper bridge. -/
theorem upper_bound_bridge (x B H0 : ℝ) (n : ℕ)
    (hbound : ∀ β, S.isAlg β → S.degree β ≤ n → H0 ≤ S.height β →
      S.height β ^ (-B - 1) ≤ |x - β|) :
    S.wStar x n ≤ (B : EReal) := by
  apply iSup_le
  intro w
  apply iSup_le
  intro hw
  have hwB : w ≤ B := by
    apply le_of_not_gt
    intro hBw
    have hfinite : (S.approximants x n w).Finite :=
      (S.northcott n H0).subset (by
        intro β hβ
        rcases hβ with ⟨ha, hd, _, herr⟩
        refine ⟨ha, hd, ?_⟩
        apply le_of_not_gt
        intro hH
        have hp := Real.rpow_le_rpow_of_exponent_le (S.height_ge_one β ha)
          (show -w - 1 ≤ -B - 1 by linarith)
        exact (not_lt_of_ge (hbound β ha hd hH.le)) (herr.trans_le hp))
    exact hw hfinite
  exact_mod_cast hwB

/-- Taking all exponents strictly below W gives the lower bridge. -/
theorem lower_bound_bridge (x W : ℝ) (d : ℕ)
    (h : ∀ w < W, (S.approximants x d w).Infinite) :
    (W : EReal) ≤ S.wStar x d := by
  apply le_of_not_gt
  intro hlt
  obtain ⟨w, hlow, hhigh⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hw : w < W := by exact_mod_cast hhigh
  exact (not_lt_of_ge (S.admissible_le_wStar (h w hw))) hlow

/-- Normalization at degree zero is immaterial to the filter at infinity. -/
def normalizedWStar (x : ℝ) (n : ℕ) : EReal :=
  S.wStar x n / (n : EReal)

/-- Exactly (1.2), with transcendence relative to the algebraic interface. -/
def IsTNumber (x : ℝ) : Prop :=
  ¬ S.isAlg x ∧ (∀ n, 1 ≤ n → S.wStar x n < ⊤) ∧
    Filter.limsup (S.normalizedWStar x) Filter.atTop = ⊤

/-- Unbounded normalized exponents on every tail imply the manuscript limsup. -/
theorem t_number_bridge (x : ℝ) (htrans : ¬ S.isAlg x)
    (hfinite : ∀ n, 1 ≤ n → S.wStar x n < ⊤)
    (hunbounded : ∀ R : ℝ, ∀ N : ℕ, ∃ n ≥ N,
      (R : EReal) ≤ S.normalizedWStar x n) : S.IsTNumber x := by
  refine ⟨htrans, hfinite, ?_⟩
  apply (EReal.eq_top_iff_forall_lt _).2
  intro R
  have hle : ((R + 1 : ℝ) : EReal) ≤
      Filter.limsup (S.normalizedWStar x) Filter.atTop :=
    Filter.le_limsup_of_frequently_le
      ((Filter.frequently_atTop).2 (hunbounded (R + 1)))
  have hlt : (R : EReal) < ((R + 1 : ℝ) : EReal) := by
    exact_mod_cast (show R < R + 1 by linarith)
  exact hlt.trans_le hle

/-- The tail formulation used by the bridge is equivalent to (1.2). -/
theorem isTNumber_iff_tail_unbounded (x : ℝ) :
    S.IsTNumber x ↔ ¬ S.isAlg x ∧
      (∀ n, 1 ≤ n → S.wStar x n < ⊤) ∧
      (∀ R : ℝ, ∀ N : ℕ, ∃ n ≥ N, (R : EReal) ≤ S.normalizedWStar x n) := by
  constructor
  · rintro ⟨ht, hf, hl⟩
    refine ⟨ht, hf, ?_⟩
    intro R
    apply Filter.frequently_atTop.mp
    have hlt : (R : EReal) < Filter.limsup (S.normalizedWStar x) Filter.atTop := by
      rw [hl]
      exact EReal.coe_lt_top R
    exact (Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hlt).mono
      (fun _ h => h.le)
  · rintro ⟨ht, hf, hu⟩
    exact S.t_number_bridge x ht hf hu

end AlgebraicApproximationSystem
end TNumbersLean
